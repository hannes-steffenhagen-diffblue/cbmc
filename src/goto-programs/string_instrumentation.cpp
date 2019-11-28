/*******************************************************************\

Module: String Abstraction

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// String Abstraction

#include "string_instrumentation.h"

#include <algorithm>

#include <util/arith_tools.h>
#include <util/c_types.h>
#include <util/config.h>
#include <util/invariant.h>
#include <util/mathematical_expr.h>
#include <util/mathematical_types.h>
#include <util/message.h>
#include <util/refined_string_type.h>
#include <util/std_code.h>
#include <util/std_expr.h>
#include <util/string_constant.h>
#include <util/string_expr.h>
#include <util/symbol_table.h>

#include <goto-programs/format_strings.h>
#include <goto-programs/goto_model.h>
#include <goto-programs/remove_skip.h>

predicate_exprt is_zero_string(const exprt &what, bool write)
{
  predicate_exprt result("is_zero_string");
  result.copy_to_operands(what);
  result.set("lhs", write);
  return result;
}

exprt zero_string_length(
  const exprt &what,
  bool write)
{
  exprt result("zero_string_length", size_type());
  result.copy_to_operands(what);
  result.set("lhs", write);
  return result;
}

exprt buffer_size(const exprt &what)
{
  exprt result("buffer_size", size_type());
  result.copy_to_operands(what);
  return result;
}

class string_instrumentationt:public messaget
{
public:
  string_instrumentationt(
    symbol_tablet &_symbol_table,
    message_handlert &_message_handler):
    messaget(_message_handler),
    symbol_table(_symbol_table),
    ns(_symbol_table)
  {
  }

  void operator()(goto_programt &dest);
  void operator()(goto_functionst &dest);

protected:
  symbol_tablet &symbol_table;
  namespacet ns;

  void make_type(exprt &dest, const typet &type)
  {
    if(ns.follow(dest.type())!=ns.follow(type))
      dest = typecast_exprt(dest, type);
  }

  void instrument(goto_programt &dest, goto_programt::targett it);
  void do_function_call(goto_programt &dest, goto_programt::targett it);

  // strings
  void do_sprintf(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_snprintf(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_strcat(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_strncmp(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_strchr2(goto_functiont &strchr_function);
  refined_string_exprt char_ptr_to_refined_string(
    const exprt &char_ptr,
    goto_programt &program) const;
  void do_strchr(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_strrchr(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_strstr(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_strtok(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_strerror(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);
  void do_fscanf(
    goto_programt &dest,
    goto_programt::targett it,
    const code_function_callt &);

  void do_format_string_read(
    goto_programt &dest,
    goto_programt::const_targett target,
    const code_function_callt::argumentst &arguments,
    std::size_t format_string_inx,
    std::size_t argument_start_inx,
    const std::string &function_name);

  void do_format_string_write(
    goto_programt &dest,
    goto_programt::const_targett target,
    const code_function_callt::argumentst &arguments,
    std::size_t format_string_inx,
    std::size_t argument_start_inx,
    const std::string &function_name);

  bool is_string_type(const typet &t) const
  {
    return
      (t.id()==ID_pointer || t.id()==ID_array) &&
      (t.subtype().id()==ID_signedbv || t.subtype().id()==ID_unsignedbv) &&
      (to_bitvector_type(t.subtype()).get_width()==config.ansi_c.char_width);
  }

  void invalidate_buffer(
    goto_programt &dest,
    goto_programt::const_targett target,
    const exprt &buffer,
    const typet &buf_type,
    const mp_integer &limit);
};

void string_instrumentation(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  goto_programt &dest)
{
  string_instrumentationt string_instrumentation(symbol_table, message_handler);
  string_instrumentation(dest);
}

void string_instrumentation(
  symbol_tablet &symbol_table,
  message_handlert &message_handler,
  goto_functionst &dest)
{
  string_instrumentationt string_instrumentation(symbol_table, message_handler);
  string_instrumentation(dest);
}

void string_instrumentation(
  goto_modelt &goto_model,
  message_handlert &message_handler)
{
  string_instrumentation(
    goto_model.symbol_table,
    message_handler,
    goto_model.goto_functions);
}

void string_instrumentationt::operator()(goto_functionst &dest)
{
  for(goto_functionst::function_mapt::iterator
      it=dest.function_map.begin();
      it!=dest.function_map.end();
      it++)
  {
    if(it->first == "strchr")
    {
      do_strchr2(it->second);
    }
    (*this)(it->second.body);
  }
}

void string_instrumentationt::operator()(goto_programt &dest)
{
  Forall_goto_program_instructions(it, dest)
    instrument(dest, it);
}

void string_instrumentationt::instrument(
  goto_programt &dest,
  goto_programt::targett it)
{
  if(it->is_function_call())
    do_function_call(dest, it);
}

void string_instrumentationt::do_function_call(
  goto_programt &dest,
  goto_programt::targett target)
{
  const code_function_callt &call = target->get_function_call();
  const exprt &function = call.function();
  // const exprt &lhs=call.lhs();

  if(function.id()==ID_symbol)
  {
    const irep_idt &identifier=
      to_symbol_expr(function).get_identifier();

    if(identifier=="strcoll")
    {
    }
    else if(identifier=="strncmp")
      do_strncmp(dest, target, call);
    else if(identifier=="strxfrm")
    {
    }
    //    else if(identifier=="strchr")
    //      do_strchr(dest, target, call);
    else if(identifier=="strcspn")
    {
    }
    else if(identifier=="strpbrk")
    {
    }
    // else if(identifier=="strrchr")
    //   do_strrchr(dest, target, call);
    else if(identifier=="strspn")
    {
    }
    else if(identifier=="strerror")
      do_strerror(dest, target, call);
    else if(identifier=="strstr")
      do_strstr(dest, target, call);
    else if(identifier=="strtok")
      do_strtok(dest, target, call);
    else if(identifier=="sprintf")
      do_sprintf(dest, target, call);
    else if(identifier=="snprintf")
      do_snprintf(dest, target, call);
    else if(identifier=="fscanf")
      do_fscanf(dest, target, call);

    remove_skip(dest);
  }
}

void string_instrumentationt::do_sprintf(
  goto_programt &dest,
  goto_programt::targett target,
  const code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()<2)
  {
    throw incorrect_source_program_exceptiont(
      "sprintf expected to have two or more arguments",
      target->source_location);
  }

  goto_programt tmp;

  // in the abstract model, we have to report a
  // (possibly false) positive here
  goto_programt::targett assertion = tmp.add(
    goto_programt::make_assertion(false_exprt(), target->source_location));
  assertion->source_location.set_property_class("string");
  assertion->source_location.set_comment("sprintf buffer overflow");

  do_format_string_read(tmp, target, arguments, 1, 2, "sprintf");

  if(call.lhs().is_not_nil())
  {
    exprt rhs =
      side_effect_expr_nondett(call.lhs().type(), target->source_location);

    tmp.add(
      goto_programt::make_assignment(call.lhs(), rhs, target->source_location));
  }

  target->turn_into_skip();
  dest.insert_before_swap(target, tmp);
}

void string_instrumentationt::do_snprintf(
  goto_programt &dest,
  goto_programt::targett target,
  const code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()<3)
  {
    throw incorrect_source_program_exceptiont(
      "snprintf expected to have three or more arguments",
      target->source_location);
  }

  goto_programt tmp;

  exprt bufsize = buffer_size(arguments[0]);

  goto_programt::targett assertion = tmp.add(goto_programt::make_assertion(
    binary_relation_exprt(bufsize, ID_ge, arguments[1]),
    target->source_location));
  assertion->source_location.set_property_class("string");
  assertion->source_location.set_comment("snprintf buffer overflow");

  do_format_string_read(tmp, target, arguments, 2, 3, "snprintf");

  if(call.lhs().is_not_nil())
  {
    exprt rhs =
      side_effect_expr_nondett(call.lhs().type(), target->source_location);

    tmp.add(
      goto_programt::make_assignment(call.lhs(), rhs, target->source_location));
  }

  target->turn_into_skip();
  dest.insert_before_swap(target, tmp);
}

void string_instrumentationt::do_fscanf(
  goto_programt &dest,
  goto_programt::targett target,
  const code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()<2)
  {
    throw incorrect_source_program_exceptiont(
      "fscanf expected to have two or more arguments", target->source_location);
  }

  goto_programt tmp;

  do_format_string_write(tmp, target, arguments, 1, 2, "fscanf");

  if(call.lhs().is_not_nil())
  {
    exprt rhs =
      side_effect_expr_nondett(call.lhs().type(), target->source_location);

    tmp.add(
      goto_programt::make_assignment(call.lhs(), rhs, target->source_location));
  }

  target->turn_into_skip();
  dest.insert_before_swap(target, tmp);
}

void string_instrumentationt::do_format_string_read(
  goto_programt &dest,
  goto_programt::const_targett target,
  const code_function_callt::argumentst &arguments,
  std::size_t format_string_inx,
  std::size_t argument_start_inx,
  const std::string &function_name)
{
  const exprt &format_arg=arguments[format_string_inx];

  if(
    format_arg.id() == ID_address_of &&
    to_address_of_expr(format_arg).object().id() == ID_index &&
    to_index_expr(to_address_of_expr(format_arg).object()).array().id() ==
      ID_string_constant)
  {
    format_token_listt token_list = parse_format_string(id2string(
      to_string_constant(
        to_index_expr(to_address_of_expr(format_arg).object()).array())
        .get_value()));

    std::size_t args=0;

    for(const auto &token : token_list)
    {
      if(token.type==format_tokent::token_typet::STRING)
      {
        const exprt &arg=arguments[argument_start_inx+args];

        if(arg.id()!=ID_string_constant) // we don't need to check constants
        {
          exprt temp(arg);

          if(arg.type().id() != ID_pointer)
          {
            index_exprt index(temp, from_integer(0, index_type()));
            temp=address_of_exprt(index);
          }

          goto_programt::targett assertion =
            dest.add(goto_programt::make_assertion(
              is_zero_string(temp), target->source_location));
          assertion->source_location.set_property_class("string");
          std::string comment("zero-termination of string argument of ");
          comment += function_name;
          assertion->source_location.set_comment(comment);
        }
      }

      if(token.type!=format_tokent::token_typet::TEXT &&
         token.type!=format_tokent::token_typet::UNKNOWN) args++;

      if(find(
           token.flags.begin(),
           token.flags.end(),
           format_tokent::flag_typet::ASTERISK)!=
         token.flags.end())
        args++; // just eat the additional argument
    }
  }
  else // non-const format string
  {
    goto_programt::targett format_ass = dest.add(goto_programt::make_assertion(
      is_zero_string(arguments[1]), target->source_location));
    format_ass->source_location.set_property_class("string");
    format_ass->source_location.set_comment(
      "zero-termination of format string of " + function_name);

    for(std::size_t i=2; i<arguments.size(); i++)
    {
      const exprt &arg=arguments[i];

      if(arguments[i].id() != ID_string_constant && is_string_type(arg.type()))
      {
        exprt temp(arg);

        if(arg.type().id() != ID_pointer)
        {
          index_exprt index(temp, from_integer(0, index_type()));
          temp=address_of_exprt(index);
        }

        goto_programt::targett assertion =
          dest.add(goto_programt::make_assertion(
            is_zero_string(temp), target->source_location));
        assertion->source_location.set_property_class("string");
        assertion->source_location.set_comment(
          "zero-termination of string argument of " + function_name);
      }
    }
  }
}

void string_instrumentationt::do_format_string_write(
  goto_programt &dest,
  goto_programt::const_targett target,
  const code_function_callt::argumentst &arguments,
  std::size_t format_string_inx,
  std::size_t argument_start_inx,
  const std::string &function_name)
{
  const exprt &format_arg=arguments[format_string_inx];

  if(
    format_arg.id() == ID_address_of &&
    to_address_of_expr(format_arg).object().id() == ID_index &&
    to_index_expr(to_address_of_expr(format_arg).object()).array().id() ==
      ID_string_constant) // constant format
  {
    format_token_listt token_list = parse_format_string(id2string(
      to_string_constant(
        to_index_expr(to_address_of_expr(format_arg).object()).array())
        .get_value()));

    std::size_t args=0;

    for(const auto &token : token_list)
    {
      if(find(
           token.flags.begin(),
           token.flags.end(),
           format_tokent::flag_typet::ASTERISK)!=
         token.flags.end())
        continue; // asterisk means `ignore this'

      switch(token.type)
      {
        case format_tokent::token_typet::STRING:
        {
          const exprt &argument=arguments[argument_start_inx+args];
          const typet &arg_type = argument.type();

          exprt condition;

          if(token.field_width!=0)
          {
            exprt fwidth=from_integer(token.field_width, unsigned_int_type());
            exprt one=from_integer(1, unsigned_int_type());
            const plus_exprt fw_1(fwidth, one); // +1 for 0-char

            exprt fw_lt_bs;

            if(arg_type.id()==ID_pointer)
              fw_lt_bs=
                binary_relation_exprt(fw_1, ID_le, buffer_size(argument));
            else
            {
              const index_exprt index(
                argument, from_integer(0, unsigned_int_type()));
              address_of_exprt aof(index);
              fw_lt_bs=binary_relation_exprt(fw_1, ID_le, buffer_size(aof));
            }

            condition = fw_lt_bs;
          }
          else
          {
            // this is a possible overflow.
            condition = false_exprt();
          }

          goto_programt::targett assertion = dest.add(
            goto_programt::make_assertion(condition, target->source_location));
          assertion->source_location.set_property_class("string");
          std::string comment("format string buffer overflow in ");
          comment += function_name;
          assertion->source_location.set_comment(comment);

          // now kill the contents
          invalidate_buffer(
            dest, target, argument, arg_type, token.field_width);

          args++;
          break;
        }
        case format_tokent::token_typet::TEXT:
        case format_tokent::token_typet::UNKNOWN:
        {
          // nothing
          break;
        }
        case format_tokent::token_typet::POINTER:
        case format_tokent::token_typet::CHAR:
        case format_tokent::token_typet::FLOAT:
        case format_tokent::token_typet::INT:
        {
          const exprt &argument=arguments[argument_start_inx+args];
          const dereference_exprt lhs{argument};

          side_effect_expr_nondett rhs(lhs.type(), target->source_location);

          dest.add(
            goto_programt::make_assignment(lhs, rhs, target->source_location));

          args++;
          break;
        }
      }
    }
  }
  else // non-const format string
  {
    for(std::size_t i=argument_start_inx; i<arguments.size(); i++)
    {
      const typet &arg_type = arguments[i].type();

      // Note: is_string_type() is a `good guess' here. Actually
      // any of the pointers could point into an array. But it
      // would suck if we had to invalidate all variables.
      // Luckily this case isn't needed too often.
      if(is_string_type(arg_type))
      {
        // as we don't know any field width for the %s that
        // should be here during runtime, we just report a
        // possibly false positive
        goto_programt::targett assertion =
          dest.add(goto_programt::make_assertion(
            false_exprt(), target->source_location));
        assertion->source_location.set_property_class("string");
        std::string comment("format string buffer overflow in ");
        comment += function_name;
        assertion->source_location.set_comment(comment);

        invalidate_buffer(dest, target, arguments[i], arg_type, 0);
      }
      else
      {
        dereference_exprt lhs{arguments[i]};

        side_effect_expr_nondett rhs(lhs.type(), target->source_location);

        dest.add(
          goto_programt::make_assignment(lhs, rhs, target->source_location));
      }
    }
  }
}

void string_instrumentationt::do_strncmp(
  goto_programt &,
  goto_programt::targett,
  const code_function_callt &)
{
}

refined_string_exprt string_instrumentationt::char_ptr_to_refined_string(
  const exprt &char_ptr,
  goto_programt &program) const
{
  auto new_aux_symbol =
    [](
      const irep_idt &name,
      const typet &type,
      symbol_table_baset &symbol_table) -> auxiliary_symbolt {
    auxiliary_symbolt new_symbol;
    new_symbol.base_name = name;
    new_symbol.pretty_name = name;
    new_symbol.is_static_lifetime = false;
    new_symbol.is_state_var = false;
    new_symbol.mode = ID_C;
    new_symbol.name = name;
    new_symbol.type = type;
    symbol_table.add(new_symbol);

    return new_symbol;
  };

  const auto length_symbol = new_aux_symbol(
    "cprover_string_index_of_func::string_length", index_type(), symbol_table);
  const auto length_field = length_symbol.symbol_expr();
  const auto content_symbol = new_aux_symbol(
    "cprover_string_index_of_func::string_content",
    char_ptr.type(),
    symbol_table);
  const auto content_field = content_symbol.symbol_expr();
  const auto array_type = to_pointer_type(char_ptr.type());

  program.add(goto_programt::make_decl(length_symbol.symbol_expr()));
  program.add(goto_programt::make_decl(content_symbol.symbol_expr()));

  const auto refined_string_type =
    refined_string_typet{index_type(), array_type};

  const auto refined_string_expr =
    refined_string_exprt{length_field, content_field, refined_string_type};

  program.add(goto_programt::make_assignment(
    refined_string_expr.length(),
    side_effect_expr_nondett{length_symbol.type}));
  program.add(
    goto_programt::make_assignment(refined_string_expr.content(), char_ptr));

  //TODO : read max-nondet-string-length from options
  program.add(goto_programt::make_assumption(binary_relation_exprt{
    refined_string_expr.length(), ID_le, from_integer(10, index_type())}));

  //  const exprt &array = char_ptr; //TODO : maybe
  //----------
  const array_typet nondet_array_type{char_type(),
                                      infinity_exprt(index_type())};
  const symbolt data_sym = new_aux_symbol(
    "nondet_infinite_array_pointer",
    pointer_type(nondet_array_type),
    symbol_table);
  const symbol_exprt data_pointer = data_sym.symbol_expr();
  program.add(goto_programt::make_decl(data_pointer));
  dereference_exprt nondet_array_expr{data_pointer};
  //----------
  const address_of_exprt array_pointer(
    index_exprt(nondet_array_expr, from_integer(0, index_type())));
  program.add(goto_programt::make_assignment(
    array_pointer, refined_string_expr.content()));

  const symbolt return_sym_length =
    new_aux_symbol("return_array_length", index_type(), symbol_table);
  const auto return_length_expr = return_sym_length.symbol_expr();
  program.add(goto_programt::make_decl(return_length_expr));

  const std::vector<typet> associate_length_to_array_argument_types = {
    nondet_array_expr.type(), length_symbol.type};

  const auto apply_associate_length_to_array = function_application_exprt{
    symbol_exprt{ID_cprover_associate_length_to_array_func,
                 mathematical_function_typet{
                   std::move(associate_length_to_array_argument_types),
                   return_sym_length.type}},
    {nondet_array_expr, refined_string_expr.length()},
    index_type()};

  program.add(goto_programt::make_assignment(
    return_length_expr, apply_associate_length_to_array));

  const symbolt return_sym_pointer =
    new_aux_symbol("return_array_pointer", index_type(), symbol_table);
  const auto return_pointer_expr = return_sym_pointer.symbol_expr();
  program.add(goto_programt::make_decl(return_pointer_expr));

  const std::vector<typet> associate_pointer_to_array_argument_types = {
    nondet_array_expr.type(), array_pointer.type()};

  const auto apply_associate_pointer_to_array = function_application_exprt{
    symbol_exprt{ID_cprover_associate_array_to_pointer_func,
                 mathematical_function_typet{
                   std::move(associate_pointer_to_array_argument_types),
                   return_sym_pointer.type}},
    {nondet_array_expr, array_pointer},
    index_type()};

  program.add(goto_programt::make_assignment(
    return_pointer_expr, apply_associate_pointer_to_array));

  // program.add(goto_programt::make_assignment(
  //   refined_string_expr.content(), array_pointer));

  return refined_string_exprt{refined_string_expr.length(),
                              //      array_pointer};
                              refined_string_expr.content()};
}

void string_instrumentationt::do_strchr2(goto_functiont &strchr_function)
{
  const auto &params = to_code_type(strchr_function.type).parameters();
  const auto &str_param = params.at(0);
  const auto &ch_param = params.at(1);

  goto_programt new_body;

  auto new_aux_symbol =
    [](
      const irep_idt &name,
      const typet &type,
      symbol_table_baset &symbol_table) -> auxiliary_symbolt {
    auxiliary_symbolt new_symbol;
    new_symbol.base_name = name;
    new_symbol.pretty_name = name;
    new_symbol.is_static_lifetime = false;
    new_symbol.is_state_var = false;
    new_symbol.mode = ID_C;
    new_symbol.name = name;
    new_symbol.type = type;
    symbol_table.add(new_symbol);

    return new_symbol;
  };

  std::vector<typet> argument_types;
  for(const auto &arg : params)
    argument_types.push_back(arg.type());

  // const auto func_symbol = new_aux_symbol(
  //   ID_cprover_string_index_of_func,
  //   mathematical_function_typet(std::move(argument_types), size_type()),
  //   symbol_table);

  const auto refined_string_type =
    refined_string_typet{index_type(), to_pointer_type(str_param.type())};

  const auto str_param_symbol =
    symbol_exprt{str_param.get_identifier(), str_param.type()};
  const auto ch_param_symbol =
    symbol_exprt{ch_param.get_identifier(), ch_param.type()};

  exprt::operandst refined_arguments;
  refined_arguments.push_back(
    char_ptr_to_refined_string(str_param_symbol, new_body));
  // struct_exprt{
  //   {
  //     from_integer(4,signed_int_type()),
  //       str_param_symbol}, refined_string_type});
  refined_arguments.push_back(ch_param_symbol);

  const auto apply_index_of = function_application_exprt(
    symbol_exprt{
      ID_cprover_string_c_index_of_func,
      mathematical_function_typet(std::move(argument_types), index_type())},
    refined_arguments,
    index_type());

  const auto maybe_return =
    new_aux_symbol("maybe_return", index_type(), symbol_table);

  new_body.add(goto_programt::make_assignment(
    code_assignt{maybe_return.symbol_expr(), apply_index_of}));

  auto found_case = new_body.add(goto_programt::make_return(code_returnt{
    plus_exprt{str_param_symbol,
               typecast_exprt{maybe_return.symbol_expr(), size_type()}}}));

  auto jump_to_found_case = new_body.insert_before(
    found_case,
    goto_programt::make_goto(
      found_case,
      binary_relation_exprt{
        maybe_return.symbol_expr(), ID_ge, from_integer(0, index_type())}));

  auto return_null = new_body.insert_after(
    jump_to_found_case,
    goto_programt::make_return(
      code_returnt{null_pointer_exprt{to_pointer_type(str_param.type())}}));

  auto end_function = new_body.add(goto_programt::make_end_function());
  new_body.insert_after(
    return_null, goto_programt::make_goto(end_function, true_exprt{}));

  // new_body.add(goto_programt::make_return(code_returnt{
  //   plus_exprt{str_param_symbol,
  //              typecast_exprt{maybe_return.symbol_expr(), size_type()}}}));

  // new_body.add(goto_programt::make_return(code_returnt{
  //    plus_exprt{str_param_symbol,
  //        from_integer(0, signed_int_type())}}));

  strchr_function.body = std::move(new_body);
}

void string_instrumentationt::do_strchr(
  goto_programt &dest,
  goto_programt::targett target,
  const code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    throw incorrect_source_program_exceptiont(
      "strchr expected to have two arguments", target->source_location);
  }

  goto_programt tmp;

  auto new_aux_symbol =
    [](
      const irep_idt &name,
      const typet &type,
      symbol_table_baset &symbol_table) -> auxiliary_symbolt {
    auxiliary_symbolt new_symbol;
    new_symbol.base_name = name;
    new_symbol.pretty_name = name;
    new_symbol.is_static_lifetime = false;
    new_symbol.is_state_var = false;
    new_symbol.mode = ID_C;
    new_symbol.name = name;
    new_symbol.type = type;
    symbol_table.add(new_symbol);

    return new_symbol;
  };

  const auto length_symbol =
    new_aux_symbol("strchr_arg_length", size_type(), symbol_table);

  std::vector<typet> argument_types;
  for(const auto &arg : arguments)
    argument_types.push_back(arg.type());

  const auto func_symbol = new_aux_symbol(
    ID_cprover_string_c_index_of_func,
    mathematical_function_typet(std::move(argument_types), size_type()),
    symbol_table);

  const auto &string_arg = arguments.at(0);
  const auto refined_string_type =
    refined_string_typet{size_type(), to_pointer_type(string_arg.type())};

  exprt::operandst refined_arguments;
  refined_arguments.push_back(struct_exprt{
    {length_symbol.symbol_expr(), string_arg}, refined_string_type});
  refined_arguments.push_back(arguments.at(1));

  const auto apply_index_of = function_application_exprt(
    func_symbol.symbol_expr(), refined_arguments, size_type());

  tmp.add(goto_programt::make_assignment(
    target->get_function_call().lhs(), plus_exprt{string_arg, apply_index_of}));

  target->turn_into_skip();
  dest.insert_before_swap(target, tmp);
}

void string_instrumentationt::do_strrchr(
  goto_programt &dest,
  goto_programt::targett target,
  const code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    throw incorrect_source_program_exceptiont(
      "strrchr expected to have two arguments", target->source_location);
  }

  goto_programt tmp;

  goto_programt::targett assertion = tmp.add(goto_programt::make_assertion(
    is_zero_string(arguments[0]), target->source_location));
  assertion->source_location.set_property_class("string");
  assertion->source_location.set_comment(
    "zero-termination of string argument of strrchr");

  target->turn_into_skip();
  dest.insert_before_swap(target, tmp);
}

void string_instrumentationt::do_strstr(
  goto_programt &dest,
  goto_programt::targett target,
  const code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    throw incorrect_source_program_exceptiont(
      "strstr expected to have two arguments", target->source_location);
  }

  goto_programt tmp;

  goto_programt::targett assertion0 = tmp.add(goto_programt::make_assertion(
    is_zero_string(arguments[0]), target->source_location));
  assertion0->source_location.set_property_class("string");
  assertion0->source_location.set_comment(
    "zero-termination of 1st string argument of strstr");

  goto_programt::targett assertion1 = tmp.add(goto_programt::make_assertion(
    is_zero_string(arguments[1]), target->source_location));
  assertion1->source_location.set_property_class("string");
  assertion1->source_location.set_comment(
    "zero-termination of 2nd string argument of strstr");

  target->turn_into_skip();
  dest.insert_before_swap(target, tmp);
}

void string_instrumentationt::do_strtok(
  goto_programt &dest,
  goto_programt::targett target,
  const code_function_callt &call)
{
  const code_function_callt::argumentst &arguments=call.arguments();

  if(arguments.size()!=2)
  {
    throw incorrect_source_program_exceptiont(
      "strtok expected to have two arguments", target->source_location);
  }

  goto_programt tmp;

  goto_programt::targett assertion0 = tmp.add(goto_programt::make_assertion(
    is_zero_string(arguments[0]), target->source_location));
  assertion0->source_location.set_property_class("string");
  assertion0->source_location.set_comment(
    "zero-termination of 1st string argument of strtok");

  goto_programt::targett assertion1 = tmp.add(goto_programt::make_assertion(
    is_zero_string(arguments[1]), target->source_location));
  assertion1->source_location.set_property_class("string");
  assertion1->source_location.set_comment(
    "zero-termination of 2nd string argument of strtok");

  target->turn_into_skip();
  dest.insert_before_swap(target, tmp);
}

void string_instrumentationt::do_strerror(
  goto_programt &dest,
  goto_programt::targett it,
  const code_function_callt &call)
{
  if(call.lhs().is_nil())
  {
    it->turn_into_skip();
    return;
  }

  irep_idt identifier_buf="__strerror_buffer";
  irep_idt identifier_size="__strerror_buffer_size";

  if(symbol_table.symbols.find(identifier_buf)==symbol_table.symbols.end())
  {
    symbolt new_symbol_size;
    new_symbol_size.base_name="__strerror_buffer_size";
    new_symbol_size.pretty_name=new_symbol_size.base_name;
    new_symbol_size.name=identifier_size;
    new_symbol_size.mode=ID_C;
    new_symbol_size.type=size_type();
    new_symbol_size.is_state_var=true;
    new_symbol_size.is_lvalue=true;
    new_symbol_size.is_static_lifetime=true;

    array_typet type(char_type(), new_symbol_size.symbol_expr());
    symbolt new_symbol_buf;
    new_symbol_buf.mode=ID_C;
    new_symbol_buf.type=type;
    new_symbol_buf.is_state_var=true;
    new_symbol_buf.is_lvalue=true;
    new_symbol_buf.is_static_lifetime=true;
    new_symbol_buf.base_name="__strerror_buffer";
    new_symbol_buf.pretty_name=new_symbol_buf.base_name;
    new_symbol_buf.name=new_symbol_buf.base_name;

    symbol_table.insert(std::move(new_symbol_buf));
    symbol_table.insert(std::move(new_symbol_size));
  }

  const symbolt &symbol_size=ns.lookup(identifier_size);
  const symbolt &symbol_buf=ns.lookup(identifier_buf);

  goto_programt tmp;

  {
    exprt nondet_size =
      side_effect_expr_nondett(size_type(), it->source_location);
    tmp.add(goto_programt::make_assignment(
      code_assignt(symbol_size.symbol_expr(), nondet_size),
      it->source_location));

    tmp.add(goto_programt::make_assumption(
      binary_relation_exprt(
        symbol_size.symbol_expr(),
        ID_notequal,
        from_integer(0, symbol_size.type)),
      it->source_location));
  }

  // return a pointer to some magic buffer
  index_exprt index(
    symbol_buf.symbol_expr(),
    from_integer(0, index_type()),
    char_type());

  address_of_exprt ptr(index);

  // make that zero-terminated
  tmp.add(goto_programt::make_assignment(
    is_zero_string(ptr, true), true_exprt(), it->source_location));

  // assign address
  {
    exprt rhs=ptr;
    make_type(rhs, call.lhs().type());
    tmp.add(goto_programt::make_assignment(
      code_assignt(call.lhs(), rhs), it->source_location));
  }

  it->turn_into_skip();
  dest.insert_before_swap(it, tmp);
}

void string_instrumentationt::invalidate_buffer(
  goto_programt &dest,
  goto_programt::const_targett target,
  const exprt &buffer,
  const typet &buf_type,
  const mp_integer &limit)
{
  irep_idt cntr_id="string_instrumentation::$counter";

  if(symbol_table.symbols.find(cntr_id)==symbol_table.symbols.end())
  {
    symbolt new_symbol;
    new_symbol.base_name="$counter";
    new_symbol.pretty_name=new_symbol.base_name;
    new_symbol.name=cntr_id;
    new_symbol.mode=ID_C;
    new_symbol.type=size_type();
    new_symbol.is_state_var=true;
    new_symbol.is_lvalue=true;
    new_symbol.is_static_lifetime=true;

    symbol_table.insert(std::move(new_symbol));
  }

  const symbolt &cntr_sym=ns.lookup(cntr_id);

  // create a loop that runs over the buffer
  // and invalidates every element

  dest.add(goto_programt::make_assignment(
    cntr_sym.symbol_expr(),
    from_integer(0, cntr_sym.type),
    target->source_location));

  exprt bufp;

  if(buf_type.id()==ID_pointer)
    bufp=buffer;
  else
  {
    index_exprt index(
      buffer, from_integer(0, index_type()), buf_type.subtype());
    bufp=address_of_exprt(index);
  }

  exprt condition;

  if(limit==0)
    condition =
      binary_relation_exprt(cntr_sym.symbol_expr(), ID_ge, buffer_size(bufp));
  else
    condition = binary_relation_exprt(
      cntr_sym.symbol_expr(), ID_gt, from_integer(limit, unsigned_int_type()));

  goto_programt::targett check = dest.add(
    goto_programt::make_incomplete_goto(condition, target->source_location));

  goto_programt::targett invalidate = dest.add(goto_programt::instructiont(
    static_cast<const codet &>(get_nil_irep()),
    target->source_location,
    ASSIGN,
    nil_exprt(),
    {}));

  const plus_exprt plus(
    cntr_sym.symbol_expr(), from_integer(1, unsigned_int_type()));

  dest.add(goto_programt::make_assignment(
    cntr_sym.symbol_expr(), plus, target->source_location));

  dest.add(
    goto_programt::make_goto(check, true_exprt(), target->source_location));

  goto_programt::targett exit =
    dest.add(goto_programt::make_skip(target->source_location));

  check->complete_goto(exit);

  const plus_exprt b_plus_i(bufp, cntr_sym.symbol_expr());
  const dereference_exprt deref(b_plus_i, buf_type.subtype());

  const side_effect_expr_nondett nondet(
    buf_type.subtype(), target->source_location);

  invalidate->code=code_assignt(deref, nondet);
}
