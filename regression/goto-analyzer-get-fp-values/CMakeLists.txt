add_test_pl_tests(
    "${CMAKE_CURRENT_LIST_DIR}/chain.sh $<TARGET_FILE:goto-analyzer> $<TARGET_FILE:goto-cc> $<TARGET_FILE:goto-instrument> $<TARGET_FILE:cbmc>"
)