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

exprt recursive_nondet_thing::get_initialiser(const typet &type, std::size_t depth, code_blockt &body)
{
  if(type.id() == ID_struct_tag)
  {
    return get_struct_tag_initializer(to_struct_tag_type(type), depth, body);
  } else if(type.id() == ID_pointer) {
    return get_pointer_initializer(to_pointer_type(type), depth, body);
  } else {
    return get_nondet_initializer(type, depth, body);
  }
}


symbol_exprt recursive_nondet_thing::get_malloc_function() {
  std::clog << "getting malloc function" << std::endl;
  auto malloc_sym = goto_model.symbol_table.lookup("malloc");
  if(malloc_sym == nullptr) {
    std::clog << "malloc not found in symbol table, adding..." << std::endl;
    symbolt new_malloc_sym;
    new_malloc_sym.type = code_typet{
      code_typet{{code_typet::parametert{size_type()}},
                 pointer_type(empty_typet{})}
    };
    new_malloc_sym.name = new_malloc_sym.pretty_name = new_malloc_sym.base_name
      = "malloc";
    new_malloc_sym.mode = ID_C;
    goto_model.symbol_table.insert(new_malloc_sym);
    // goto_model.goto_functions.function_map["malloc"].type =
    //   to_code_type(new_malloc_sym.type);
    return new_malloc_sym.symbol_expr();
  }
  return malloc_sym->symbol_expr();
}


exprt recursive_nondet_thing::get_struct_tag_initializer(const struct_tag_typet& type, std::size_t depth, code_blockt& body)
{
  allocate_objectst allocate_objects{ID_C, type.source_location(), "initializer", goto_model.symbol_table};
  auto struct_var = allocate_objects.allocate_automatic_local_object(type, "struct_var");
  allocate_objects.declare_created_symbols(body);
  auto const &ns = namespacet{goto_model.symbol_table};
  for(auto const &component : ns.follow_tag(type).components())
  {
    body.add(code_assignt{member_exprt{struct_var, component},
     get_initialiser(component.type(), depth, body)});
  }
  return struct_var;
}

exprt recursive_nondet_thing::get_pointer_initializer( const pointer_typet &type, std::size_t depth, code_blockt &body)
{
  INVARIANT(options.min_null_tree_depth <= options.max_nondet_tree_depth,
    "the min tree depth can't be greater than the max nondet tree depth");
  allocate_objectst allocate_objects{ID_C, type.source_location(), "initializer", goto_model.symbol_table};
  exprt choice;
  if(depth >= options.min_null_tree_depth && depth <= options.max_nondet_tree_depth)
  {
    choice = allocate_objects.allocate_automatic_local_object(bool_typet{}, "choice");
  }
  auto pointer = allocate_objects.allocate_automatic_local_object(type, "pointer");
  allocate_objects.declare_created_symbols(body);
  body.add(code_assignt{pointer, null_pointer_exprt{type}});
  auto malloc_function = get_malloc_function();
  auto const &ns = namespacet{goto_model.symbol_table};
  if(depth < options.min_null_tree_depth) {
    body.add(code_assignt{pointer, typecast_exprt{side_effect_expr_function_callt{malloc_function,
     {size_of_expr(type.subtype(), ns)},
     to_code_type(malloc_function.type()).return_type()}, type}});
    body.add(code_assignt{dereference_exprt{pointer}, get_initialiser(type.subtype(), depth+1, body)});
  } else if(depth <= options.max_nondet_tree_depth) {
    code_blockt then_case{};
    then_case.add(code_assignt{pointer, typecast_exprt{side_effect_expr_function_callt{malloc_function,
     {size_of_expr(type.subtype(), ns)},
     to_code_type(malloc_function.type()).return_type()}, type}});
    then_case.add(code_assignt{dereference_exprt{pointer}, get_initialiser(type.subtype(), depth + 1, then_case)});
    body.add(code_ifthenelset{choice, then_case});
  }
  return pointer;
}

exprt recursive_nondet_thing::get_nondet_initializer(const typet& type, std::size_t depth, code_blockt &body)
{
  return side_effect_expr_nondett{type};
}