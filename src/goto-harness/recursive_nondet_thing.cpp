#include "recursive_nondet_thing.h"

#include <goto-programs/goto_convert_functions.h>
#include <util/allocate_objects.h>
#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/cprover_prefix.h>
#include <util/fresh_symbol.h>
#include <util/irep.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/pointer_offset_size.h>

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
  }
  else if(type.id() == ID_pointer)
  {
    constructor_name = make_pointer_constructor(to_pointer_type(type));
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
                   this->get_initialiser(component.type(), depth_symbol)});
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
    "goto_harness",
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
    "goto_harness",
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

irep_idt
recursive_nondet_thing::make_pointer_constructor(const pointer_typet &type)
{
  auto &constructor = register_constructor_for_type(type);
  auto constructor_body = code_blockt{};
  auto const depth_param = get_depth_param_from_constructor(constructor);
  auto allocate_objects = allocate_objectst{
    ID_C, type.source_location(), constructor.name, goto_model.symbol_table};
  auto const ns = namespacet{goto_model.symbol_table};
  auto const pointer_val =
    allocate_objects.allocate_automatic_local_object(type);
  auto const nondet_choose_to_recurse =
    allocate_objects.allocate_automatic_local_object(bool_typet{});
  auto const malloc_function = get_malloc_function();
  allocate_objects.declare_created_symbols(constructor_body);
  constructor_body.add(code_assignt{nondet_choose_to_recurse,
                                    side_effect_expr_nondett{bool_typet{}}});
  auto allocate_and_initialize_object = code_blockt{};
  allocate_and_initialize_object.add(code_assignt{
    pointer_val,
    typecast_exprt{side_effect_expr_function_callt{
                     malloc_function, {size_of_expr(type.subtype(), ns)}},
                   type}});
  allocate_and_initialize_object.add(code_assignt{
    dereference_exprt{pointer_val, type.subtype()},
    get_initialiser(
      type.subtype(),
      plus_exprt{depth_param, from_integer(1, depth_param.type())})});
  auto const set_pointer_to_null =
    code_assignt{pointer_val, from_integer(0, pointer_val.type())};
  constructor_body.add(code_ifthenelset{
    and_exprt{
      binary_relation_exprt{
        depth_param,
        ID_le,
        from_integer(options.max_nondet_tree_depth, depth_param.type())},
      or_exprt{binary_relation_exprt{
                 depth_param,
                 ID_lt,
                 from_integer(options.min_null_tree_depth, depth_param.type())},
               nondet_choose_to_recurse}},
    allocate_and_initialize_object,
    set_pointer_to_null});
  constructor_body.add(code_returnt{pointer_val});
  constructor.value = std::move(constructor_body);
  return constructor.name;
}

symbol_exprt recursive_nondet_thing::get_depth_param_from_constructor(
  const symbolt &constructor)
{
  return goto_model.symbol_table
    .lookup_ref(to_code_type(constructor.type).parameter_identifiers().front())
    .symbol_expr();
}

symbol_exprt recursive_nondet_thing::get_malloc_function() {
  auto malloc_sym = goto_model.symbol_table.lookup("malloc");
  if(malloc_sym == nullptr) {
    symbolt new_malloc_sym;
    new_malloc_sym.type = code_typet{
      code_typet{{code_typet::parametert{size_type()}},
                 pointer_type(empty_typet{})}
    };
    new_malloc_sym.name = new_malloc_sym.pretty_name = new_malloc_sym.base_name
      = "malloc";
    new_malloc_sym.mode = ID_C;
    goto_model.symbol_table.insert(new_malloc_sym);
    return new_malloc_sym.symbol_expr();
  }
  return malloc_sym->symbol_expr();
}
