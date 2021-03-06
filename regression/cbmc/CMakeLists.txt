if("${CMAKE_CXX_COMPILER_ID}" STREQUAL "MSVC")
  set(gcc_only -X gcc-only)
else()
  set(gcc_only "")
endif()

if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  set(exclude_win_broken_tests -X winbug)
else()
  set(exclude_win_broken_tests "")
endif()

add_test_pl_tests(
    "$<TARGET_FILE:cbmc> --validate-goto-model --validate-ssa-equation" -X smt-backend ${gcc_only} ${exclude_win_broken_tests}
)

add_test_pl_profile(
    "cbmc-paths-lifo"
    "$<TARGET_FILE:cbmc> --paths lifo"
    "-C;-X;thorough-paths;-X;smt-backend;-X;paths-lifo-expected-failure;-s;paths-lifo"
    "CORE"
    ${gcc_only}
)

if("${CMAKE_SYSTEM_NAME}" STREQUAL "Windows")
  message(WARNING "Tests are failing on windows under this config, for reasons unknown. Investigation is pending.")
else()
  add_test_pl_profile(
    "cbmc-cprover-smt2"
    "$<TARGET_FILE:cbmc> --cprover-smt2"
    "-C;-X;broken-smt-backend;-s;cprover-smt2"
    "CORE"
    ${gcc_only}
    )

  set_property(
    TEST "cbmc-cprover-smt2-CORE"
    PROPERTY ENVIRONMENT
      "PATH=$ENV{PATH}:${CMAKE_BINARY_DIR}/bin"
  )
endif()
