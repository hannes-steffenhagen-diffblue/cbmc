/*******************************************************************\

Module: C Nondet Symbol Factory

Author: Diffblue Ltd.

\*******************************************************************/

/// \file
/// C Nondet Symbol Factory

#include "c_nondet_symbol_factory.h"

#include <ansi-c/c_object_factory_parameters.h>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/fresh_symbol.h>
#include <util/namespace.h>
#include <util/nondet_bool.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/std_types.h>
#include <util/string_constant.h>

#include <goto-programs/goto_functions.h>
#include <util/array_name.h>
#include <util/optional_utilities.h>

class symbol_factoryt
{
  std::vector<const symbolt *> &symbols_created;
  symbol_tablet &symbol_table;
  const source_locationt &loc;
  namespacet ns;
  const c_object_factory_parameterst &object_factory_params;
  std::map<irep_idt, irep_idt> &deferred_array_sizes;

  typedef std::set<irep_idt> recursion_sett;

public:
  symbol_factoryt(
    std::vector<const symbolt *> &_symbols_created,
    symbol_tablet &_symbol_table,
    const source_locationt &loc,
    const c_object_factory_parameterst &object_factory_params,
    std::map<irep_idt, irep_idt> &deferred_array_sizes)
    : symbols_created(_symbols_created),
      symbol_table(_symbol_table),
      loc(loc),
      ns(_symbol_table),
      object_factory_params(object_factory_params),
      deferred_array_sizes(deferred_array_sizes)
  {}

  exprt allocate_object(
    code_blockt &assignments,
    const exprt &target_expr,
    const typet &allocate_type,
    const bool static_lifetime);

  void gen_nondet_init(
    code_blockt &assignments,
    const exprt &expr,
    const std::size_t depth = 0,
    recursion_sett recursion_set = recursion_sett());

private:
  symbolt &new_tmp_symbol(const typet &type, const std::string &prefix);
  void gen_nondet_array_init(
    code_blockt &assignments,
    const exprt &expr,
    std::size_t depth,
    const recursion_sett &recursion_set);

  void gen_nondet_size_array_init(
    code_blockt &assignments,
    const symbol_exprt &array,
    const size_t depth,
    const recursion_sett &recursion_set);

  void defer_size_initialization(irep_idt associated_size_name, irep_idt array_size_name);
  optionalt<dstringt> get_deferred_size(irep_idt symbol_name) const;
};

/// Create a symbol for a pointer to point to
/// \param assignments: The code block to add code to
/// \param target_expr: The expression which we are allocating a symbol for
/// \param allocate_type: The type to use for the symbol. If this doesn't match
///   target_expr then a cast will be used for the assignment
/// \param static_lifetime: Whether the symbol created should have static
///   lifetime
/// \return Returns the address of the allocated symbol
exprt symbol_factoryt::allocate_object(
  code_blockt &assignments,
  const exprt &target_expr,
  const typet &allocate_type,
  const bool static_lifetime)
{
  symbolt &aux_symbol = get_fresh_aux_symbol(
    allocate_type,
    id2string(loc.get_function()),
    "tmp",
    loc,
    ID_C,
    symbol_table);
  aux_symbol.is_static_lifetime = static_lifetime;
  symbols_created.push_back(&aux_symbol);

  const typet &allocate_type_resolved=ns.follow(allocate_type);
  const typet &target_type=ns.follow(target_expr.type().subtype());
  bool cast_needed=allocate_type_resolved!=target_type;

  exprt aoe=address_of_exprt(aux_symbol.symbol_expr());
  if(cast_needed)
  {
    aoe=typecast_exprt(aoe, target_expr.type());
  }

  // Add the following code to assignments:
  //   <target_expr> = &tmp$<temporary_counter>
  code_assignt assign(target_expr, aoe);
  assign.add_source_location()=loc;
  assignments.move(assign);

  return aoe;
}

/// Creates a nondet for expr, including calling itself recursively to make
/// appropriate symbols to point to if expr is a pointer.
/// \param assignments: The code block to add code to
/// \param expr: The expression which we are generating a non-determinate value
///   for
/// \param depth number of pointers followed so far during initialisation
/// \param recursion_set names of structs seen so far on current pointer chain
void symbol_factoryt::gen_nondet_init(
  code_blockt &assignments,
  const exprt &expr,
  const std::size_t depth,
  recursion_sett recursion_set)
{
  const typet &type=ns.follow(expr.type());

  if(type.id()==ID_pointer)
  {
    if(expr.id() == ID_symbol)
    {
      auto const &symbol_expr = to_symbol_expr(expr);
      const auto &symbol_name = symbol_expr.get_identifier();
      if(object_factory_params.should_be_treated_as_array(symbol_name))
      {
        gen_nondet_size_array_init(
          assignments, symbol_expr, depth, recursion_set);
        return;
      } else if(object_factory_params.is_array_size_parameter(symbol_name))
      {
        // skip, we'll handle this during array initialisation
        return;
      }
    }
    // dereferenced type
    const pointer_typet &pointer_type=to_pointer_type(type);
    const typet &subtype=ns.follow(pointer_type.subtype());

    if(subtype.id() == ID_struct)
    {
      const struct_typet &struct_type = to_struct_type(subtype);
      const irep_idt struct_tag = struct_type.get_tag();

      if(
        recursion_set.find(struct_tag) != recursion_set.end() &&
        depth >= object_factory_params.max_nondet_tree_depth)
      {
        code_assignt c(expr, null_pointer_exprt(pointer_type));
        assignments.move(c);

        return;
      }
    }

    code_blockt non_null_inst;

    exprt allocated=allocate_object(non_null_inst, expr, subtype, false);

    exprt init_expr;
    if(allocated.id()==ID_address_of)
    {
      init_expr=allocated.op0();
    }
    else
    {
      init_expr=dereference_exprt(allocated, allocated.type().subtype());
    }
    gen_nondet_init(non_null_inst, init_expr, depth + 1, recursion_set);

    if(depth < object_factory_params.min_null_tree_depth)
    {
      // Add the following code to assignments:
      // <expr> = <aoe>;
      assignments.append(non_null_inst);
    }
    else
    {
      // Add the following code to assignments:
      //           IF !NONDET(_Bool) THEN GOTO <label1>
      //           <expr> = <null pointer>
      //           GOTO <label2>
      // <label1>: <expr> = &tmp$<temporary_counter>;
      //           <code from recursive call to gen_nondet_init() with
      //             tmp$<temporary_counter>>
      // And the next line is labelled label2
      auto set_null_inst=code_assignt(expr, null_pointer_exprt(pointer_type));
      set_null_inst.add_source_location()=loc;

      code_ifthenelset null_check;
      null_check.cond() = side_effect_expr_nondett(bool_typet(), loc);
      null_check.then_case()=set_null_inst;
      null_check.else_case()=non_null_inst;

      assignments.move(null_check);
    }
  }
  else if(type.id() == ID_struct)
  {
    const struct_typet &struct_type = to_struct_type(type);

    const irep_idt struct_tag = struct_type.get_tag();

    recursion_set.insert(struct_tag);

    for(const auto &component : struct_type.components())
    {
      const typet &component_type = component.type();
      const irep_idt name = component.get_name();

      member_exprt me(expr, name, component_type);
      me.add_source_location() = loc;

      gen_nondet_init(assignments, me, depth, recursion_set);
    }
  }
  else if(type.id() == ID_array)
  {
    gen_nondet_array_init(assignments, expr, depth, recursion_set);
  }
  else
  {
    // If type is a ID_c_bool then add the following code to assignments:
    //   <expr> = NONDET(_BOOL);
    // Else add the following code to assignments:
    //   <expr> = NONDET(type);
    exprt rhs = type.id() == ID_c_bool ? get_nondet_bool(type, loc)
                                       : side_effect_expr_nondett(type, loc);
    code_assignt assign(expr, rhs);
    assign.add_source_location()=loc;
    if(expr.id() == ID_symbol) {
      auto const &symbol_expr = to_symbol_expr(expr);
      auto const associated_array_size = get_deferred_size(symbol_expr.get_identifier());
      if(associated_array_size.has_value()) {
        assign.rhs() = typecast_exprt{
          symbol_table.lookup_ref(associated_array_size.value()).symbol_expr(),
          symbol_expr.type()
        };
      }
    }
    assignments.move(assign);
  }
}

void symbol_factoryt::gen_nondet_size_array_init(
  code_blockt &assignments,
  const symbol_exprt &array,
  const size_t depth,
  const symbol_factoryt::recursion_sett &recursion_set)
{
  // This works on dynamic arrays, so the thing we assign to is a pointer
  // rather than an array with a fixed size
  PRECONDITION(array.type().id() == ID_pointer);
  // Create code like this:
  // size_t cond;
  // size_t actual_size;
  // T* array;
  // if(cond < 1) {
  //   actual_size = 1;
  //   array = calloc(actual_size, sizeof(T));
  //   for(size_t i = 0; i < actual_size; ++i) {
  //      array[i] = nondet();
  //   }
  // } else if(cond < 2) {
  //   ....
  // }
  // ...
  // else {
  //   actual_size = max_array_size;
  //   ...
  // }
  auto const max_array_size =
    std::size_t{object_factory_params.max_dynamic_array_size};
  auto const &array_name = array.get_identifier();
  auto const &size_cond_symbol = new_tmp_symbol(size_type(), "size_cond");
  auto const &size_symbol = new_tmp_symbol(size_type(), "size");

  auto const &element_type = array.type().subtype();
  code_ifthenelset initialization_if_then_else;
  auto *current_if_then_else = &initialization_if_then_else;

  for(std::size_t i = 1; i < max_array_size; ++i)
  {
    auto const &array_size = from_integer(i, size_type());
    auto array_type = array_typet{element_type, array_size};

    auto &static_array = new_tmp_symbol(
      array_type, id2string(array_name) + "_" + std::__cxx11::to_string(i));
    static_array.is_static_lifetime = true;

    const constant_exprt &size_expr = array_size;

    current_if_then_else->cond() = binary_exprt(
      size_cond_symbol.symbol_expr(), ID_lt, size_expr, bool_typet{});
    code_blockt then_case;
    then_case.add(code_assignt(size_symbol.symbol_expr(), size_expr));
    gen_nondet_array_init(
      then_case, static_array.symbol_expr(), depth, recursion_set);
    then_case.add(
      code_assignt{array,
                   address_of_exprt{index_exprt{static_array.symbol_expr(),
                                                from_integer(0, size_type()),
                                                array_type.subtype()},
                                    pointer_type(array_type.subtype())}});
    current_if_then_else->then_case() = then_case;
    if(i + 1 < max_array_size)
    {
      current_if_then_else->else_case() = code_ifthenelset{};
      current_if_then_else = reinterpret_cast<code_ifthenelset *>(
        &current_if_then_else->else_case());
    }
    else
    {
      // generate an else case instead of another if on the final case
      auto const &array_size = from_integer(i + 1, size_type());
      auto array_type = array_typet{element_type, array_size};

      auto &static_array = new_tmp_symbol(
        array_type,
        id2string(array_name) + "_" + std::__cxx11::to_string(i + 1));
      static_array.is_static_lifetime = true;

      const constant_exprt &size_expr = array_size;
      code_blockt else_case;
      else_case.add(code_assignt(size_symbol.symbol_expr(), size_expr));
      gen_nondet_array_init(
        else_case, static_array.symbol_expr(), depth, recursion_set);
      else_case.add(
        code_assignt{array,
                     address_of_exprt{index_exprt{static_array.symbol_expr(),
                                                  from_integer(0, size_type()),
                                                  array_type.subtype()},
                                      pointer_type(array_type.subtype())}});
      current_if_then_else->else_case() = else_case;
    }
  }
  assignments.add(initialization_if_then_else);
  auto const associated_size = object_factory_params.get_associated_size_variable(array_name);
  if(associated_size.has_value()) {
    auto const associated_size_symbol = symbol_table.lookup(associated_size.value());
    if(associated_size_symbol != nullptr) {
      assignments.add(code_assignt{
        associated_size_symbol->symbol_expr(),
        typecast_exprt{size_symbol.symbol_expr(), associated_size_symbol->type}
      });
    } else {
      // we've not seen the associated size symbol yet, so we have
      // to defer setting it to when we do get there...
      defer_size_initialization(associated_size.value(), size_symbol.name);
    }
  }
}

void symbol_factoryt::gen_nondet_array_init(
  code_blockt &assignments,
  const exprt &expr,
  std::size_t depth,
  const recursion_sett &recursion_set)
{
  auto const &array_type = to_array_type(expr.type());
  auto const array_size = numeric_cast_v<mp_integer>(array_type.size());
  DATA_INVARIANT(array_size >= 0, "Arrays should have non-negative size");
  for(auto index = mp_integer(0); index < array_size; ++index)
  {
    gen_nondet_init(
      assignments,
      index_exprt{expr, from_integer(index, size_type())},
      depth,
      recursion_set);
  }
}

symbolt &
symbol_factoryt::new_tmp_symbol(const typet &type, const std::string &prefix)
{
  auto &symbol = get_fresh_aux_symbol(
    type,
    id2string(object_factory_params.function_id),
    prefix,
    loc,
    ID_C,
    symbol_table);
  symbols_created.push_back(&symbol);
  return symbol;
}

void symbol_factoryt::defer_size_initialization(irep_idt associated_size_name, irep_idt array_size_name) {
  auto succeeded =
    deferred_array_sizes.insert({associated_size_name, array_size_name});
  INVARIANT(succeeded.second,
    "each size parameter should have a unique associated array");
}

optionalt<dstringt> symbol_factoryt::get_deferred_size(irep_idt symbol_name) const {
  return optional_lookup(deferred_array_sizes, symbol_name);
}

/// Creates a symbol and generates code so that it can vary over all possible
/// values for its type. For pointers this involves allocating symbols which it
/// can point to.
/// \param init_code: The code block to add generated code to
/// \param symbol_table: The symbol table
/// \param base_name: The name to use for the symbol created
/// \param type: The type for the symbol created
/// \param loc: The location to assign to generated code
/// \return Returns the symbol_exprt for the symbol created
exprt c_nondet_symbol_factory(
  code_blockt &init_code,
  symbol_tablet &symbol_table,
  const irep_idt base_name,
  const typet &type,
  const source_locationt &loc,
  const c_object_factory_parameterst &object_factory_parameters,
  std::map<irep_idt, irep_idt> &deferred_array_sizes)
{
  irep_idt identifier=id2string(goto_functionst::entry_point())+
    "::"+id2string(base_name);

  auxiliary_symbolt main_symbol;
  main_symbol.mode=ID_C;
  main_symbol.is_static_lifetime=false;
  main_symbol.name=identifier;
  main_symbol.base_name=base_name;
  main_symbol.type=type;
  main_symbol.location=loc;

  symbol_exprt main_symbol_expr=main_symbol.symbol_expr();

  symbolt *main_symbol_ptr;
  bool moving_symbol_failed=symbol_table.move(main_symbol, main_symbol_ptr);
  CHECK_RETURN(!moving_symbol_failed);

  std::vector<const symbolt *> symbols_created;
  symbols_created.push_back(main_symbol_ptr);

  symbol_factoryt state(
    symbols_created,
    symbol_table,
    loc,
    object_factory_parameters,
    deferred_array_sizes);
  code_blockt assignments;
  state.gen_nondet_init(assignments, main_symbol_expr);

  // Add the following code to init_code for each symbol that's been created:
  //   <type> <identifier>;
  for(const symbolt * const symbol_ptr : symbols_created)
  {
    code_declt decl(symbol_ptr->symbol_expr());
    decl.add_source_location()=loc;
    init_code.move(decl);
  }

  init_code.append(assignments);

  // Add the following code to init_code for each symbol that's been created:
  //   INPUT("<identifier>", <identifier>);
  for(symbolt const *symbol_ptr : symbols_created)
  {
    codet input_code(ID_input);
    input_code.operands().resize(2);
    input_code.op0()=
      address_of_exprt(index_exprt(
        string_constantt(symbol_ptr->base_name),
        from_integer(0, index_type())));
    input_code.op1()=symbol_ptr->symbol_expr();
    input_code.add_source_location()=loc;
    init_code.move(input_code);
  }

  return std::move(main_symbol_expr);
}
