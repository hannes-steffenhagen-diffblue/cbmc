/******************************************************************\

Module: harness generator for functions

Author: Diffblue Ltd.

\******************************************************************/

#include "function_call_harness_generator.h"

#include <goto-programs/goto_convert.h>
#include <goto-programs/goto_model.h>
#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/exception_utils.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/ui_message.h>

#include "function_harness_generator_options.h"
#include "goto_harness_parse_options.h"
#include "recursive_nondet_thing.h"

struct function_call_harness_generatort::implt
{
  ui_message_handlert *message_handler;
  irep_idt function;
  irep_idt harness_function_name;
  symbol_tablet *symbol_table;
  goto_functionst *goto_functions;
  bool nondet_globals = false;
  std::unique_ptr<recursive_nondet_thing> thing;

  void generate(goto_modelt &goto_model, const irep_idt &harness_function_name);
  void generate_nondet_globals(code_blockt &function_body);
  void setup_parameters_and_call_entry_function(code_blockt &function_body);
  const symbolt &lookup_function_to_call();
  void generate_initialisation_code_for(code_blockt &block, const exprt &lhs);
  void ensure_harness_does_not_already_exist();
  void add_harness_function_to_goto_model(code_blockt function_body);
};

function_call_harness_generatort::function_call_harness_generatort(
  ui_message_handlert &message_handler)
  : goto_harness_generatort{}, p_impl(util_make_unique<implt>())
{
  p_impl->message_handler = &message_handler;
}

function_call_harness_generatort::~function_call_harness_generatort() = default;

void function_call_harness_generatort::handle_option(
  const std::string &option,
  const std::list<std::string> &values)
{
  if(option == FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT)
  {
    p_impl->function = require_exactly_one_value(option, values);
  }
  else if (option == FUNCTION_HARNESS_GENERATOR_NONDET_GLOBALS_OPT)
  {
    p_impl->nondet_globals = true;
  }
  else
  {
    throw invalid_command_line_argument_exceptiont{
      "function harness generator cannot handle this option", "--" + option};
  }
}

void function_call_harness_generatort::generate(
  goto_modelt &goto_model,
  const irep_idt &harness_function_name)
{
  p_impl->generate(goto_model, harness_function_name);
}

void function_call_harness_generatort::implt::setup_parameters_and_call_entry_function(
  code_blockt &function_body)
{
  const auto &function_to_call = lookup_function_to_call();
  const auto &function_type = to_code_type(function_to_call.type);
  const auto &parameters = function_type.parameters();

  code_function_callt::operandst arguments{};

  auto allocate_objects =
    allocate_objectst{function_to_call.mode, function_to_call.location, "__goto_harness",
                      *symbol_table};
  for(const auto &parameter : parameters)
  {
    auto argument = allocate_objects.allocate_automatic_local_object(
      parameter.type(), parameter.get_base_name());
    arguments.push_back(argument);
  }
  allocate_objects.declare_created_symbols(function_body);
  for(auto const &argument : arguments)
  {
    generate_initialisation_code_for(function_body, argument);
  }
  code_function_callt function_call{function_to_call.symbol_expr(), std::move(arguments)};
  function_call.add_source_location() = function_to_call.location;

  function_body.add(std::move(function_call));
}

void function_call_harness_generatort::implt::generate(
  goto_modelt &goto_model,
  const irep_idt &harness_function_name)
{
  symbol_table = &goto_model.symbol_table;
  goto_functions = &goto_model.goto_functions;
  thing = util_make_unique<recursive_nondet_thing>(
    nondet_thing_optionst{}, goto_model, *message_handler);
  this->harness_function_name = harness_function_name;
  ensure_harness_does_not_already_exist();

  // create body for the function
  code_blockt function_body{};

  generate_nondet_globals(function_body);
  setup_parameters_and_call_entry_function(function_body);
  add_harness_function_to_goto_model(std::move(function_body));
}

void function_call_harness_generatort::implt::generate_nondet_globals(
  code_blockt &function_body)
{
  if(nondet_globals)
  {
    for(const auto &symbol_table_entry : *symbol_table)
    {
      const auto &symbol = symbol_table_entry.second;
      if(
        symbol.is_static_lifetime && symbol.is_lvalue &&
        !has_prefix(id2string(symbol.name), "__CPROVER_"))
      {
        generate_initialisation_code_for(function_body, symbol.symbol_expr());
      }
    }
  }
}

void function_call_harness_generatort::implt::generate_initialisation_code_for(
  code_blockt &block,
  const exprt &lhs)
{
  block.add(code_assignt{lhs, thing->get_initialiser(lhs.type(), 
    from_integer(0, unsignedbv_typet{32}))});
}

void function_call_harness_generatort::validate_options()
{
  if(p_impl->function == ID_empty)
    throw invalid_command_line_argument_exceptiont{
      "required parameter entry function not set",
      "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT};
}

const symbolt &function_call_harness_generatort::implt::lookup_function_to_call()
{
  auto function_found = symbol_table->lookup(function);

  if(function_found == nullptr)
  {
    throw invalid_command_line_argument_exceptiont{
      "function that should be harnessed is not found " + id2string(function),
      "--" FUNCTION_HARNESS_GENERATOR_FUNCTION_OPT};
  }

  return *function_found;
}

void function_call_harness_generatort::implt::ensure_harness_does_not_already_exist()
{
  if(symbol_table->lookup(harness_function_name))
  {
    throw invalid_command_line_argument_exceptiont{
      "harness function already exists in the symbol table",
      "--" GOTO_HARNESS_GENERATOR_HARNESS_FUNCTION_NAME_OPT};
  }
}

void function_call_harness_generatort::implt::add_harness_function_to_goto_model(
  code_blockt function_body)
{
  const auto &function_to_call = symbol_table->lookup_ref(function);

  // create the function symbol
  symbolt harness_function_symbol{};
  harness_function_symbol.name = harness_function_symbol.base_name =
  harness_function_symbol.pretty_name = harness_function_name;

  harness_function_symbol.is_lvalue = true;
  harness_function_symbol.mode = function_to_call.mode;
  harness_function_symbol.type = code_typet{{}, empty_typet{}};
  harness_function_symbol.value = std::move(function_body);

  symbol_table->insert(harness_function_symbol);

  auto const &generated_harness =
    symbol_table->lookup_ref(harness_function_name);
  goto_functions->function_map[harness_function_name].type =
    to_code_type(generated_harness.type);
  auto &body =
    goto_functions->function_map[harness_function_name].body;
  goto_convert(
    static_cast<const codet &>(generated_harness.value),
    *symbol_table,
    body,
    *message_handler,
    ID_C);
  body.add(goto_programt::make_end_function());
}
