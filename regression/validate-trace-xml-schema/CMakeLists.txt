find_package(PythonInterp 3.5)
if(${PYTHONINTERP_FOUND})
    add_test(NAME validate-trace-xml-schema
            COMMAND ${PYTHON_EXECUTABLE} check.py $<TARGET_FILE:cbmc>
            WORKING_DIRECTORY ${CMAKE_CURRENT_LIST_DIR})
    set_tests_properties(validate-trace-xml-schema
            PROPERTIES
            LABELS "CBMC;CORE")
else()
    message(WARNING "Python >= 3.5 not found, skipping trace schema tests")
endif()
