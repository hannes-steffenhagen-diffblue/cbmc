#include "recursive_nondet_thing.h"

#include <goto-programs/goto_convert_functions.h>
#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/cprover_prefix.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>

// TODO: REMOVE DEBUG STUFF

#include <iostream>

exprt recursive_nondet_thing::get_initialiser(
  const typet &type,
  const exprt &depth)
{
  const auto it = constructor_for_type.find(type);
  irep_idt constructor_name;

  if (it == constructor_for_type.end())
  {
    constructor_name = make_constructor_for_type(type);
  } else {
    constructor_name = it->second;
  }

  return side_effect_expr_function_callt{
    goto_model.symbol_table.lookup_ref(constructor_name).symbol_expr(),
    {depth}};
}

irep_idt recursive_nondet_thing::make_constructor_for_type(
  const typet &type)
{
  irep_idt constructor_name;
  if(type.id() == ID_struct_tag)
  {
    constructor_name =  make_struct_constructor(to_struct_tag_type(type));
  } else {
   constructor_name =  make_nondet_constructor_for_type(type); 
  }
  finalize_constructor(goto_model.symbol_table.lookup_ref(constructor_name));
  return constructor_name;
}

irep_idt recursive_nondet_thing::make_struct_constructor(
  const struct_tag_typet &struct_tag_type)
{
  auto &constructor = register_constructor_for_type(struct_tag_type);
  auto constructor_body = code_blockt{};
  auto const depth_type = unsignedbv_typet{32};
  auto const depth_symbol =
    goto_model.symbol_table
      .lookup_ref(
        to_code_type(constructor.type).parameter_identifiers().front())
      .symbol_expr();
  auto const ns = namespacet(goto_model.symbol_table);
  auto allocate_objects = allocate_objectst{ID_C,
                                            struct_tag_type.source_location(),
                                            constructor.name,
                                            goto_model.symbol_table};
  auto const struct_val =
    allocate_objects.allocate_automatic_local_object(struct_tag_type);
  allocate_objects.declare_created_symbols(constructor_body);
  auto const &struct_type = ns.follow_tag(struct_tag_type);
  for(auto const &component : struct_type.components())
  {
    constructor_body.add(
      code_assignt{member_exprt{struct_val, component},
                   this->get_initialiser(
                     component.type(),
                     plus_exprt{depth_symbol, from_integer(1, depth_type)})});
  }
  constructor_body.add(code_returnt{struct_val});
  constructor.value = constructor_body;
  return constructor.name;
}

irep_idt recursive_nondet_thing::make_nondet_constructor_for_type(
  const typet &type)
{
  auto &constructor = register_constructor_for_type(type);
  constructor.value = code_returnt{side_effect_expr_nondett{type}};

  return constructor.name;
}

symbolt &
recursive_nondet_thing::register_constructor_for_type(const typet &type)
{
  auto parameter = code_typet::parametert{
    unsignedbv_typet{32}
  };

  auto &parameter_symbol = get_fresh_aux_symbol(
    unsignedbv_typet{32},
    CPROVER_PREFIX,
    "nondet_constructor_depth",
    type.source_location(),
    ID_C,
    goto_model.symbol_table);

  parameter.set_identifier(parameter_symbol.name);
  parameter_symbol.is_parameter = true;
  parameter_symbol.is_lvalue = true;

  symbolt &aux = get_fresh_aux_symbol(
    code_typet{{parameter}, type},
    // name_prefix
    CPROVER_PREFIX,
    // basename_prefix
    "nondet_constructor" + id2string(type.id()),
    type.source_location(),
    ID_C,
    goto_model.symbol_table);
  constructor_for_type.insert({type, aux.name});
  return aux;
}

void recursive_nondet_thing::finalize_constructor(
  const symbolt &constructor_symbol)
{
  goto_convert_functionst convert_functions(goto_model.symbol_table, message_handler);
  convert_functions.convert_function(constructor_symbol.name, goto_model.goto_functions.function_map[constructor_symbol.name]);
}