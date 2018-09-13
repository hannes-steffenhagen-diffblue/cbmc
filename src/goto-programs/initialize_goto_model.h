/*******************************************************************\

Module: Initialize a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Initialize a Goto Program

#ifndef CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
#define CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H

#include <util/message.h>
#include <util/cmdline.h>

#include "goto_model.h"
#include <string>
#include <util/exception_utils.h>

class goto_model_initialization_errort : public cprover_exceptiont
{
public:
  explicit goto_model_initialization_errort(std::string message);
  goto_model_initialization_errort(std::string message, source_locationt source_location);
  std::string what() const noexcept override;
private:
  std::string message;
  source_locationt source_location;
};

goto_modelt initialize_goto_model(
  const cmdlinet &cmdline,
  message_handlert &message_handler);

#endif // CPROVER_GOTO_PROGRAMS_INITIALIZE_GOTO_MODEL_H
