/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include "c_object_factory_parameters.h"

#include <util/cmdline.h>
#include <util/optional_utilities.h>

void parse_c_object_factory_options(const cmdlinet &cmdline, optionst &options)
{
  parse_object_factory_options(cmdline, options);
  if(cmdline.isset("pointers-to-treat-as-array"))
  {
    options.set_option(
      "pointers-to-treat-as-array",
      cmdline.get_comma_separated_values("pointers-to-treat-as-array"));
  }
  if(cmdline.isset("max-dynamic-array-size"))
  {
    options.set_option(
      "max-dynamic-array-size", cmdline.get_value("max-dynamic-array-size"));
  }
}

bool c_object_factory_parameterst::should_be_treated_as_array(irep_idt id) const
{
  return std::find(
           begin(pointers_to_treat_as_array),
           end(pointers_to_treat_as_array),
           id) != end(pointers_to_treat_as_array);
}

void c_object_factory_parameterst::set(const optionst &options)
{
  object_factory_parameterst::set(options);
  auto const &pointers_to_treat_as_array =
    options.get_list_option("pointers-to-treat-as-array");
  std::transform(
    begin(pointers_to_treat_as_array),
    end(pointers_to_treat_as_array),
    back_inserter(this->pointers_to_treat_as_array),
    id2string);
  if(options.is_set("max-dynamic-array-size"))
  {
    max_dynamic_array_size =
      options.get_unsigned_int_option("max-dynamic-array-size");
  }
}

bool c_object_factory_parameterst::is_array_size_parameter(irep_idt id) const {
  return variables_that_hold_array_sizes.find(id) != end(variables_that_hold_array_sizes);
}

optionalt<irep_idt> c_object_factory_parameterst::get_associated_size_variable(irep_idt array_id) const {
  return optional_lookup(array_name_to_associated_array_size_variable, array_id);
}

optionalt<irep_idt> c_object_factory_parameterst::get_associated_array_variable(irep_idt size_id) const {
  return optional_lookup(size_name_to_associated_array_name, size_id);
}


