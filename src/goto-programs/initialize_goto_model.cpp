#include <utility>

/*******************************************************************\

Module: Get a Goto Program

Author: Daniel Kroening, kroening@kroening.com

\*******************************************************************/

/// \file
/// Get a Goto Program

#include "initialize_goto_model.h"

#include <fstream>
#include <iostream>

#include <util/config.h>
#include <util/unicode.h>

#include <langapi/mode.h>
#include <langapi/language.h>

#include <goto-programs/rebuild_goto_start_function.h>
#include <util/exception_utils.h>

#include "goto_convert_functions.h"
#include "read_goto_binary.h"

goto_modelt initialize_goto_model(
  const cmdlinet &cmdline,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  const std::vector<std::string> &files=cmdline.args;
  if(files.empty())
  {
    throw invalid_user_input_exceptiont("missing program argument",
      "",
      "one or more paths to program files");
  }

  std::vector<std::string> binaries, sources;
  binaries.reserve(files.size());
  sources.reserve(files.size());

  for(const auto &file : files)
  {
    if(is_goto_binary(file))
      binaries.push_back(file);
    else
      sources.push_back(file);
  }

  language_filest language_files;
  language_files.set_message_handler(message_handler);

  goto_modelt goto_model;

  if(!sources.empty())
  {
    for(const auto &filename : sources)
    {
      #ifdef _MSC_VER
      std::ifstream infile(widen(filename));
      #else
      std::ifstream infile(filename);
      #endif

      if(!infile)
      {
        throw system_exceptiont(
          "failed to open input file `" + filename + '\'');
      }

      language_filet &lf=language_files.add_file(filename);
      lf.language=get_language_from_filename(filename);

      if(lf.language==nullptr)
      {

        source_locationt location;
        location.set_file(filename);
        throw goto_model_initialization_errort(
          "failed to figure out type of file", location);
      }

      languaget &language=*lf.language;
      language.set_message_handler(message_handler);
      language.get_language_options(cmdline);

      msg.status() << "Parsing " << filename << messaget::eom;

      if(language.parse(infile, filename))
      {
        throw goto_model_initialization_errort("language parsing failed");
      }

      lf.get_modules();
    }

    msg.status() << "Converting" << messaget::eom;

    if(language_files.typecheck(goto_model.symbol_table))
    {
      throw goto_model_initialization_errort(
        "type-checking of interfaces/files/modules failed");
    }
  }

  for(const auto &file : binaries)
  {
    msg.status() << "Reading GOTO program from file" << messaget::eom;

    if(read_object_and_link(file, goto_model, message_handler)) {
      throw goto_model_initialization_errort(
        "failed to read object or link in file `" + file + '\'');
    }
  }

  bool binaries_provided_start=
    goto_model.symbol_table.has_symbol(goto_functionst::entry_point());

  bool entry_point_generation_failed=false;

  if(binaries_provided_start && cmdline.isset("function"))
  {
    // Rebuild the entry-point, using the language annotation of the
    // existing __CPROVER_start function:
    rebuild_goto_start_functiont rebuild_existing_start(
      cmdline,
      goto_model,
      msg.get_message_handler());
    entry_point_generation_failed=rebuild_existing_start();
  }
  else if(!binaries_provided_start)
  {
    // Unsure of the rationale for only generating stubs when there are no
    // GOTO binaries in play; simply mirroring old code in language_uit here.
    if(binaries.empty())
    {
      // Enable/disable stub generation for opaque methods
      bool stubs_enabled=cmdline.isset("generate-opaque-stubs");
      language_files.set_should_generate_opaque_method_stubs(stubs_enabled);
    }

    // Allow all language front-ends to try to provide the user-specified
    // (--function) entry-point, or some language-specific default:
    entry_point_generation_failed=
      language_files.generate_support_functions(goto_model.symbol_table);
  }

  if(entry_point_generation_failed)
  {
    throw goto_model_initialization_errort("failed to generate entry point");
  }

  if(language_files.final(goto_model.symbol_table))
  {
    throw goto_model_initialization_errort(
      "failed to finish final conversion adjustments");
  }

  msg.status() << "Generating GOTO Program" << messaget::eom;

  goto_convert(
    goto_model.symbol_table,
    goto_model.goto_functions,
    message_handler);

  // stupid hack
  config.set_object_bits_from_symbol_table(
    goto_model.symbol_table);

  return goto_model;
}

goto_model_initialization_errort::goto_model_initialization_errort(std::string message)
  : goto_model_initialization_errort(std::move(message), source_locationt())
{}

std::string goto_model_initialization_errort::what() const noexcept {
  std::string what_msg = message;
  if(source_location.is_not_nil())
  {
    what_msg += "\nsource location: " + source_location.as_string();
  }
  return what_msg;
}

goto_model_initialization_errort::goto_model_initialization_errort(std::string message, source_locationt source_location)
  : message(std::move(message)), source_location(std::move(source_location))
{

}
