/*******************************************************************\

Module: Bounded Model Checking Utilities

Author: Daniel Kroening, Peter Schrammel

\*******************************************************************/

/// \file
/// Bounded Model Checking Utilities

#include "bmc_util.h"

#include <fstream>
#include <iostream>

#include <goto-programs/graphml_witness.h>
#include <goto-programs/json_goto_trace.h>
#include <goto-programs/xml_goto_trace.h>

#include <goto-symex/build_goto_trace.h>
#include <goto-symex/memory_model_pso.h>
#include <goto-symex/slice.h>
#include <goto-symex/symex_target_equation.h>

#include <linking/static_lifetime_init.h>

#include <solvers/decision_procedure.h>

#include <util/make_unique.h>
#include <util/ui_message.h>
#include <fresh_symbol.h>

#include "goto_symex_property_decider.h"
#include "symex_bmc.h"

void message_building_error_trace(messaget &log)
{
  log.status() << "Building error trace" << messaget::eom;
}

void build_error_trace(
  goto_tracet &goto_trace,
  const namespacet &ns,
  const symex_target_equationt &symex_target_equation,
  const decision_proceduret &decision_procedure,
  ui_message_handlert &ui_message_handler)
{
  messaget log(ui_message_handler);
  message_building_error_trace(log);

  build_goto_trace(symex_target_equation, decision_procedure, ns, goto_trace);
}

ssa_step_predicatet
ssa_step_matches_failing_property(const irep_idt &property_id)
{
  return [property_id](
           symex_target_equationt::SSA_stepst::const_iterator step,
           const decision_proceduret &decision_procedure) {
    return step->is_assert() && step->get_property_id() == property_id &&
           decision_procedure.get(step->cond_handle).is_false();
  };
}

void output_error_trace(
  const goto_tracet &goto_trace,
  const namespacet &ns,
  const trace_optionst &trace_options,
  ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  switch(ui_message_handler.get_ui())
  {
  case ui_message_handlert::uit::PLAIN:
    msg.result() << "Counterexample:" << messaget::eom;
    show_goto_trace(msg.result(), ns, goto_trace, trace_options);
    msg.result() << messaget::eom;
    break;

  case ui_message_handlert::uit::XML_UI:
  {
    xmlt xml;
    convert(ns, goto_trace, xml);
    msg.status() << xml;
  }
  break;

  case ui_message_handlert::uit::JSON_UI:
  {
    json_stream_objectt &json_result =
      ui_message_handler.get_json_stream().push_back_stream_object();
    const goto_trace_stept &step = goto_trace.steps.back();
    json_result["property"] =
      json_stringt(step.pc->source_location.get_property_id());
    json_result["description"] =
      json_stringt(step.pc->source_location.get_comment());
    json_result["status"] = json_stringt("failed");
    json_stream_arrayt &json_trace =
      json_result.push_back_stream_array("trace");
    convert<json_stream_arrayt>(ns, goto_trace, json_trace, trace_options);
  }
  break;
  }
}

/// outputs an error witness in graphml format
void output_graphml(
  const goto_tracet &goto_trace,
  const namespacet &ns,
  const optionst &options)
{
  const std::string graphml = options.get_option("graphml-witness");
  if(graphml.empty())
    return;

  graphml_witnesst graphml_witness(ns);
  graphml_witness(goto_trace);

  if(graphml == "-")
    write_graphml(graphml_witness.graph(), std::cout);
  else
  {
    std::ofstream out(graphml);
    write_graphml(graphml_witness.graph(), out);
  }
}

/// outputs a proof in graphml format
void output_graphml(
  const symex_target_equationt &symex_target_equation,
  const namespacet &ns,
  const optionst &options)
{
  const std::string graphml = options.get_option("graphml-witness");
  if(graphml.empty())
    return;

  graphml_witnesst graphml_witness(ns);
  graphml_witness(symex_target_equation);

  if(graphml == "-")
    write_graphml(graphml_witness.graph(), std::cout);
  else
  {
    std::ofstream out(graphml);
    write_graphml(graphml_witness.graph(), out);
  }
}

void convert_symex_target_equation(
  symex_target_equationt &equation,
  decision_proceduret &decision_procedure,
  message_handlert &message_handler)
{
  messaget msg(message_handler);
  msg.status() << "converting SSA" << messaget::eom;

  equation.convert(decision_procedure);
}

std::unique_ptr<memory_model_baset>
get_memory_model(const optionst &options, const namespacet &ns)
{
  const std::string mm = options.get_option("mm");

  if(mm.empty() || mm == "sc")
    return util_make_unique<memory_model_sct>(ns);
  else if(mm == "tso")
    return util_make_unique<memory_model_tsot>(ns);
  else if(mm == "pso")
    return util_make_unique<memory_model_psot>(ns);
  else
  {
    throw "invalid memory model '" + mm + "': use one of sc, tso, pso";
  }
}

void setup_symex(
  symex_bmct &symex,
  const namespacet &ns,
  const optionst &options,
  ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);
  const symbolt *init_symbol;
  if(!ns.lookup(INITIALIZE_FUNCTION, init_symbol))
    symex.language_mode = init_symbol->mode;

  msg.status() << "Starting Bounded Model Checking" << messaget::eom;

  symex.last_source_location.make_nil();

  symex.unwindset.parse_unwind(options.get_option("unwind"));
  symex.unwindset.parse_unwindset(options.get_list_option("unwindset"));
}

void slice(
  symex_bmct &symex,
  symex_target_equationt &symex_target_equation,
  const namespacet &ns,
  const optionst &options,
  ui_message_handlert &ui_message_handler)
{
  messaget msg(ui_message_handler);

  // any properties to check at all?
  if(symex_target_equation.has_threads())
  {
    // we should build a thread-aware SSA slicer
    msg.statistics() << "no slicing due to threads" << messaget::eom;
  }
  else
  {
    if(options.get_bool_option("slice-formula"))
    {
      ::slice(symex_target_equation);
      msg.statistics() << "slicing removed "
                       << symex_target_equation.count_ignored_SSA_steps()
                       << " assignments" << messaget::eom;
    }
    else
    {
      if(options.get_bool_option("simple-slice"))
      {
        simple_slice(symex_target_equation);
        msg.statistics() << "simple slicing removed "
                         << symex_target_equation.count_ignored_SSA_steps()
                         << " assignments" << messaget::eom;
      }
    }
  }
  msg.statistics() << "Generated " << symex.get_total_vccs() << " VCC(s), "
                   << symex.get_remaining_vccs()
                   << " remaining after simplification" << messaget::eom;
}

void update_properties_status_from_symex_target_equation(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties,
  const symex_target_equationt &equation)
{
  for(const auto &step : equation.SSA_steps)
  {
    if(!step.is_assert())
      continue;

    irep_idt property_id = step.get_property_id();
    CHECK_RETURN(!property_id.empty());

    // Don't update status of properties that are constant 'false';
    // we wouldn't have traces for them.
    const auto status = step.cond_expr.is_true() ? property_statust::PASS
                                                 : property_statust::UNKNOWN;
    auto emplace_result = properties.emplace(
      property_id, property_infot{step.source.pc, step.comment, status});

    if(emplace_result.second)
    {
      updated_properties.insert(property_id);
    }
    else
    {
      property_infot &property_info = emplace_result.first->second;
      property_statust old_status = property_info.status;
      property_info.status |= status;

      if(property_info.status != old_status)
        updated_properties.insert(property_id);
    }
  }
}

void update_status_of_not_checked_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  for(auto &property_pair : properties)
  {
    if(property_pair.second.status == property_statust::NOT_CHECKED)
    {
      // This could be a NOT_CHECKED, NOT_REACHABLE or PASS,
      // but the equation doesn't give us precise information.
      property_pair.second.status = property_statust::PASS;
      updated_properties.insert(property_pair.first);
    }
  }
}

void update_status_of_unknown_properties(
  propertiest &properties,
  std::unordered_set<irep_idt> &updated_properties)
{
  for(auto &property_pair : properties)
  {
    if(property_pair.second.status == property_statust::UNKNOWN)
    {
      // This could have any status except NOT_CHECKED.
      // We consider them PASS because we do verification modulo bounds.
      property_pair.second.status = property_statust::PASS;
      updated_properties.insert(property_pair.first);
    }
  }
}

void output_coverage_report(
  const std::string &cov_out,
  const abstract_goto_modelt &goto_model,
  const symex_bmct &symex,
  ui_message_handlert &ui_message_handler)
{
  if(
    !cov_out.empty() &&
    symex.output_coverage_report(goto_model.get_goto_functions(), cov_out))
  {
    messaget log(ui_message_handler);
    log.error() << "Failed to write symex coverage report to '" << cov_out
                << "'" << messaget::eom;
  }
}

__attribute__((used))
static void debug_dump_ssa_step(const SSA_stept &step, std::ostream &out)
{
    static const char *type_to_string[] =
            {
                    "NONE",
                    "ASSIGNMENT",
                    "ASSUME",
                    "ASSERT",
                    "GOTO",
                    "LOCATION",
                    "INPUT",
                    "OUTPUT",
                    "DECL",
                    "DEAD",
                    "FUNCTION_CALL",
                    "FUNCTION_RETURN",
                    "CONSTRAINT",
                    "SHARED_READ",
                    "SHARED_WRITE",
                    "SPAWN",
                    "MEMORY_BARRIER",
                    "ATOMIC_BEGIN",
                    "ATOMIC_END"
            };
    static const char *assignment_type_to_string[] =
            {
                    "STATE",
                    "HIDDEN",
                    "VISIBLE_ACTUAL_PARAMETER",
                    "HIDDEN_ACTUAL_PARAMETER",
                    "PHI",
                    "GUARD",
            };
    out << "[SSA_step " << type_to_string[static_cast<std::size_t>(step.type)]
      << "\n  ssa_lhs={" << format(step.ssa_lhs) << "}"
      << "\n  ssa_full_lhs={" << format(step.ssa_full_lhs) << "}"
      << "\n  ssa_original_full_lhs={" << format(step.original_full_lhs) << "}"
      << "\n  ssa_rhs={" << format(step.ssa_rhs) << "}"
      << "\n  guard={" << format(step.guard) << "}"
      << "\n  guard_handle={" << format(step.guard_handle) << "}"
      << "\n  cond_expr={" << format(step.cond_expr) << "}"
      << "\n  cond_handle={" << format(step.cond_handle) << "}"
      << "\n  assignment_type={" << assignment_type_to_string[static_cast<std::size_t>(step.assignment_type)] << "}"
      << '\n';
}

static void cse_dereference(symex_target_equationt &equation, symbol_tablet &symbol_table)
{
    std::ofstream out{"/tmp/debug_out.txt"};
  std::unordered_map<exprt, symbol_exprt, irep_hash> dereference_cache{};
  for(auto it = equation.SSA_steps.rbegin(); it != equation.SSA_steps.rend(); ++it)
  {
      out << "[DEBUG] SSA_step pre:\n";
      debug_dump_ssa_step(*it, out);
      const namespacet ns{symbol_table};
    auto cse_dereference_cache_rec = [&](exprt &expr) {
      // I think this breaks sharing, needs fixing
      expr.visit_pre([&](exprt &expr_pre) {
        // cache expressions of the form (p == &obj : ...)
        if(auto if_expr = expr_try_dynamic_cast<if_exprt>(expr_pre))
        {
          if(
            auto equal_expr =
              expr_try_dynamic_cast<equal_exprt>(if_expr->cond()))
          {
            if(can_cast_expr<address_of_exprt>(equal_expr->op1()))
            {
              auto cached = dereference_cache.find(expr_pre);
              if(cached == dereference_cache.end())
              {
                  auto const &cache_symbol = get_fresh_aux_symbol(
                          expr_pre.type(),
                          "symex",
                          "dereference_cache",
                          expr_pre.source_location(),
                          ID_C,
                          ns,
                          symbol_table);
                  auto cache_symbol_expr = cache_symbol.symbol_expr();
                  cache_symbol_expr.set(ID_C_SSA_symbol, ID_1);
                  equation.assignment(
                          true_exprt{},
                          to_ssa_expr(cache_symbol_expr),
                          cache_symbol_expr,
                          cache_symbol.symbol_expr(),
                          expr_pre,
                          it->source,
                          symex_targett::assignment_typet::HIDDEN);
                  auto insert_result = dereference_cache.emplace(expr_pre, cache_symbol_expr);
                  CHECK_RETURN(insert_result.second);
                  cached = insert_result.first;
              }
              expr_pre = cached->second;
            }
          }
        }
      });
    };
    cse_dereference_cache_rec(it->ssa_rhs);
    cse_dereference_cache_rec(it->guard);
    cse_dereference_cache_rec(it->cond_expr);
    out << "[DEBUG] SSA_step post:\n";
    debug_dump_ssa_step(*it, out);
  }
  std::ofstream equation_out{"/tmp/equation.txt"};
  equation.output(equation_out);
}

void
postprocess_equation(symex_bmct &symex, symex_target_equationt &equation, const optionst &options, const namespacet &ns,
                     ui_message_handlert &ui_message_handler, symbol_tablet &symex_symbol_table)
{
  const auto postprocess_equation_start = std::chrono::steady_clock::now();
  // add a partial ordering, if required
  if(equation.has_threads())
  {
    std::unique_ptr<memory_model_baset> memory_model =
      get_memory_model(options, ns);
    (*memory_model)(equation, ui_message_handler);
  }

  messaget log(ui_message_handler);
  log.statistics() << "size of program expression: "
                   << equation.SSA_steps.size() << " steps" << messaget::eom;

  slice(symex, equation, ns, options, ui_message_handler);
  cse_dereference(equation, symex_symbol_table);

  if(options.get_bool_option("validate-ssa-equation"))
  {
    symex.validate(validation_modet::INVARIANT);
  }

  const auto postprocess_equation_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> postprocess_equation_runtime =
    std::chrono::duration<double>(
      postprocess_equation_stop - postprocess_equation_start);
  log.status() << "Runtime Postprocess Equation: "
               << postprocess_equation_runtime.count() << "s" << messaget::eom;
}

std::chrono::duration<double> prepare_property_decider(
  propertiest &properties,
  symex_target_equationt &equation,
  goto_symex_property_decidert &property_decider,
  ui_message_handlert &ui_message_handler)
{
  auto solver_start = std::chrono::steady_clock::now();

  messaget log(ui_message_handler);
  log.status()
    << "Passing problem to "
    << property_decider.get_decision_procedure().decision_procedure_text()
    << messaget::eom;

  convert_symex_target_equation(
    equation, property_decider.get_decision_procedure(), ui_message_handler);
  property_decider.update_properties_goals_from_symex_target_equation(
    properties);
  property_decider.convert_goals();

  auto solver_stop = std::chrono::steady_clock::now();
  return std::chrono::duration<double>(solver_stop - solver_start);
}

void run_property_decider(
  incremental_goto_checkert::resultt &result,
  propertiest &properties,
  goto_symex_property_decidert &property_decider,
  ui_message_handlert &ui_message_handler,
  std::chrono::duration<double> solver_runtime,
  bool set_pass)
{
  auto solver_start = std::chrono::steady_clock::now();

  messaget log(ui_message_handler);
  log.status()
    << "Running "
    << property_decider.get_decision_procedure().decision_procedure_text()
    << messaget::eom;

  property_decider.add_constraint_from_goals(
    [&properties](const irep_idt &property_id) {
      return is_property_to_check(properties.at(property_id).status);
    });

  auto const sat_solver_start = std::chrono::steady_clock::now();

  decision_proceduret::resultt dec_result = property_decider.solve();

  auto const sat_solver_stop = std::chrono::steady_clock::now();
  std::chrono::duration<double> sat_solver_runtime =
    std::chrono::duration<double>(sat_solver_stop - sat_solver_start);
  log.status() << "Runtime Solver: " << sat_solver_runtime.count() << "s"
               << messaget::eom;

  property_decider.update_properties_status_from_goals(
    properties, result.updated_properties, dec_result, set_pass);

  auto solver_stop = std::chrono::steady_clock::now();
  solver_runtime += std::chrono::duration<double>(solver_stop - solver_start);
  log.status() << "Runtime decision procedure: " << solver_runtime.count()
               << "s" << messaget::eom;

  if(dec_result == decision_proceduret::resultt::D_SATISFIABLE)
  {
    result.progress = incremental_goto_checkert::resultt::progresst::FOUND_FAIL;
  }
}
