find_package(PythonInterp 3.5)
find_program(XMLLINT xmllint)
if(${PYTHONINTERP_FOUND} AND (${XMLLINT}))
  add_test(NAME validate-trace-xml-schema
    COMMAND ${PYTHON_EXECUTABLE} check.py $<TARGET_FILE:cbmc> ${XMLLINT}
    WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR})
  set_tests_properties(validate-trace-xml-schema
    PROPERTIES
    LABELS "CBMC;CORE")
else()
  # Add a always failing test to ensure doesn't silently fail on CI
  # if dependencies aren't present
  add_test(NAME validate-trace-xml-schema
    COMMAND false
    WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR})
  set_tests_properties(validate-trace-xml-schema
    PROPERTIES
    LABELS "CBMC;CORE")
  if(NOT ${PYTHONINTERP_FOUND})
    message(WARNING "Python >= 3.5 not found, trace schema tests will fail")
  endif()
  if(NOT XMLLINT)
    message(WARNING "xmllint not found, trace schema tests will fail")
  endif()
endif()
