/*******************************************************************\

Module:

Author: Daniel Poetzl

\*******************************************************************/

#ifndef CPROVER_ANSI_C_C_OBJECT_FACTORY_PARAMETERS_H
#define CPROVER_ANSI_C_C_OBJECT_FACTORY_PARAMETERS_H

#include <algorithm>
#include <string>
#include <util/object_factory_parameters.h>
#include <util/options.h>
#include <vector>

struct c_object_factory_parameterst final : public object_factory_parameterst
{
  c_object_factory_parameterst() = default;

  explicit c_object_factory_parameterst(const optionst &options)
    : object_factory_parameterst(options)
  {
  }

  bool should_be_treated_as_array(irep_idt id) const;

  void set(const optionst &options) override;

private:
  std::vector<irep_idt> pointers_to_treat_as_array;
};

/// Parse the c object factory parameters from a given command line
/// \param cmdline Command line
/// \param [out] options The options object that will be updated
void parse_c_object_factory_options(const cmdlinet &cmdline, optionst &options);

#endif
