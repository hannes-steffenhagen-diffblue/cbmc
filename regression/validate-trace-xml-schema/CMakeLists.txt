# The Schema tests require a JDK because we use the
# Java standard libraries builtin schema validation functionality
find_package(Java COMPONENTS Development)
find_package(PythonInterp 3.5)
if(${PYTHONINTERP_FOUND}
  AND ${Java_FOUND} AND ${Java_VERSION_MAJOR} VERSION_GREATER 8)
    add_test(NAME validate-trace-xml-schema
            COMMAND ${PYTHON_EXECUTABLE} check.py $<TARGET_FILE:cbmc>
            WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR})
    set_tests_properties(validate-trace-xml-schema
            PROPERTIES
            LABELS "CBMC;CORE")
else()
    message(WARNING "JDK not found, skipping trace schema tests")
endif()
