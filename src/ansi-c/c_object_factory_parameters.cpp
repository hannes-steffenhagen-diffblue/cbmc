/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#include "c_object_factory_parameters.h"

#include <util/cmdline.h>

void parse_c_object_factory_options(const cmdlinet &cmdline, optionst &options)
{
  parse_object_factory_options(cmdline, options);
  if(cmdline.isset("pointers-to-treat-as-array"))
  {
    options.set_option(
      "pointers-to-treat-as-array",
      cmdline.get_comma_separated_values("pointers-to-treat-as-array"));
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
}
