/******************************************************************\

Module: recursive_initialization

Author: Diffblue Ltd.

\******************************************************************/

#include "recursive_initialization.h"

#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/optional.h>
#include <util/optional_utils.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

recursive_initializationt::recursive_initializationt(
  recursive_initialization_configt initialization_config,
  goto_modelt &goto_model)
  : initialization_config(std::move(initialization_config)),
    goto_model(goto_model)
{
}

void recursive_initializationt::initialize(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  auto const &type = lhs.type();
  if(type.id() == ID_struct_tag)
  {
    initialize_struct_tag(lhs, depth, known_tags, body);
  }
  else if(type.id() == ID_pointer)
  {
    initialize_pointer(lhs, depth, known_tags, body);
  }
  else if(type.id() == ID_array)
  {
    initialize_array(lhs, depth, known_tags, body);
  }
  else
  {
    initialize_nondet(lhs, depth, known_tags, body);
  }
}

symbol_exprt recursive_initializationt::get_malloc_function()
{
  // unused for now, we'll need it for arrays
  auto malloc_sym = goto_model.symbol_table.lookup("malloc");
  if(malloc_sym == nullptr)
  {
    symbolt new_malloc_sym;
    new_malloc_sym.type = code_typet{code_typet{
      {code_typet::parametert{size_type()}}, pointer_type(empty_typet{})}};
    new_malloc_sym.name = new_malloc_sym.pretty_name =
      new_malloc_sym.base_name = "malloc";
    new_malloc_sym.mode = initialization_config.mode;
    goto_model.symbol_table.insert(new_malloc_sym);
    return new_malloc_sym.symbol_expr();
  }
  return malloc_sym->symbol_expr();
}

void recursive_initializationt::initialize_struct_tag(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  PRECONDITION(lhs.type().id() == ID_struct_tag);
  auto const &type = to_struct_tag_type(lhs.type());
  auto new_known_tags = known_tags;
  new_known_tags.insert(type.get_identifier());
  auto const &ns = namespacet{goto_model.symbol_table};
  for(auto const &component : ns.follow_tag(type).components())
  {
    initialize(member_exprt{lhs, component}, depth, new_known_tags, body);
  }
}

void recursive_initializationt::initialize_pointer(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  PRECONDITION(lhs.type().id() == ID_pointer);
  auto const &type = to_pointer_type(lhs.type());
  allocate_objectst allocate_objects{initialization_config.mode,
                                     type.source_location(),
                                     "initializer",
                                     goto_model.symbol_table};
  exprt choice =
    allocate_objects.allocate_automatic_local_object(bool_typet{}, "choice");
  auto pointee =
    allocate_objects.allocate_automatic_local_object(type.subtype(), "pointee");
  allocate_objects.declare_created_symbols(body);
  body.add(code_assignt{lhs, null_pointer_exprt{type}});
  bool is_unknown_struct_tag =
    can_cast_type<tag_typet>(type.subtype()) &&
    known_tags.find(to_tag_type(type.subtype()).get_identifier()) ==
      known_tags.end();

  if(
    depth < initialization_config.max_nondet_tree_depth ||
    is_unknown_struct_tag)
  {
    if(depth < initialization_config.min_null_tree_depth)
    {
      initialize(pointee, depth + 1, known_tags, body);
      body.add(code_assignt{lhs, address_of_exprt{pointee}});
    }
    else
    {
      code_blockt then_case{};
      initialize(pointee, depth + 1, known_tags, then_case);
      then_case.add(code_assignt{lhs, address_of_exprt{pointee}});
      body.add(code_ifthenelset{choice, then_case});
    }
  }
}

void recursive_initializationt::initialize_nondet(
  const exprt &lhs,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  body.add(code_assignt{lhs, side_effect_expr_nondett{lhs.type()}});
}

void recursive_initializationt::initialize_array(
  const exprt &array,
  std::size_t depth,
  const recursion_sett &known_tags,
  code_blockt &body)
{
  PRECONDITION(array.type().id() == ID_array);
  const auto &array_type = to_array_type(array.type());
  const auto array_size = numeric_cast_v<std::size_t>(to_constant_expr(array_type.size()));
  for(std::size_t index = 0; index < array_size; index++)
  {
    initialize(
      index_exprt(array, from_integer(index, size_type())), depth, known_tags, body);
  }
}

bool recursive_initializationt::should_be_treated_as_array(const irep_idt &array_name) const
{
  return
    initialization_config.pointers_to_treat_as_arrays.find(array_name) !=
      initialization_config.pointers_to_treat_as_arrays.end();
}

bool recursive_initializationt::is_array_size_parameter(const irep_idt &cmdline_arg) const
{
  return initialization_config.variables_that_hold_array_sizes.find(cmdline_arg) !=
    initialization_config.variables_that_hold_array_sizes.end();
}

optionalt<irep_idt>
recursive_initializationt::get_associated_size_variable(const irep_idt &array_name) const
{
  return optional_lookup(
    initialization_config.array_name_to_associated_array_size_variable, array_name);
}

void recursive_initializationt::initialize_dynamic_array(
  const exprt &pointer, std::size_t depth, const recursion_sett &known_tags, code_blockt &body)
{
  PRECONDITION(pointer.type().id() == ID_pointer);
  const auto &pointer_type = to_pointer_type(pointer.type());
  allocate_objectst allocate_objects{initialization_config.mode,
                                     pointer_type.source_location(),
                                     "initializer",
                                     goto_model.symbol_table};
  auto min_array_size = initialization_config.mini_dynamic_array_size;
  auto max_array_size = initialization_config.maxi_dynamic_array_size;
  PRECONDITION(max_array_size >= min_array_size);
  std::vector<symbol_exprt> array_variables;
  auto number_of_arrays = max_array_size - min_array_size + 1;


  for (auto array_size = min_array_size; array_size < max_array_size; array_size++)
  {
    array_variables.push_back(allocate_objects.allocate_automatic_local_object(
      array_typet{pointer_type.subtype(), from_integer(array_size, size_type())},
      "array"
    ));
  }

  const auto arrays = allocate_objects.allocate_automatic_local_object(
    array_typet{pointer_type, from_integer(number_of_arrays, size_type())},
    "arrays");

  const auto nondet_index = allocate_objects.allocate_automatic_local_object(
    size_type(), "nondet_index");

  allocate_objects.declare_created_symbols(body);

  for (const auto &array_variable : array_variables)
  {
    initialize(array_variable, depth + 1, known_tags, body);
  }

  body.add(code_assumet{
    binary_relation_exprt{
      nondet_index, ID_lt, from_integer(number_of_arrays, size_type())}});

  body.add(code_assignt{
    pointer, index_exprt{arrays, nondet_index}});
}
