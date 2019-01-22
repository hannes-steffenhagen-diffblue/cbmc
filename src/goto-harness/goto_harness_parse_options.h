/******************************************************************\

Module: goto_harness_parse_options

Author: Diffblue Ltd.

\******************************************************************/

#ifndef CRPOVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H
#define CRPOVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H

#include <util/parse_options.h>
#include "goto_harness_generator_factory.h"
#include "default_goto_harness_generator_options.h"

#define GOTO_HARNESS_OPTIONS \
  "(version)" \
  GOTO_HARNESS_FACTORY_OPTIONS \
  DEFAULT_GOTO_HARNESS_GENERATOR_OPTIONS \
  // end GOTO_HARNESS_OPTIONS

class goto_harness_parse_optionst : public parse_options_baset
{
public:
  int doit() override;
  void help() override;

  goto_harness_parse_optionst(int argc, const char *argv[]);
};

#endif // CRPOVER_GOTO_HARNESS_GOTO_HARNESS_PARSE_OPTIONS_H
