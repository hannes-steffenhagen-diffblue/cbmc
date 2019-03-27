default: tests.log

include ../../src/config.inc
include ../../src/common

MEMORY_ANALYZER_EXE=../../../src/memory-analyzer/memory-analyzer
GOTO_HARNESS_EXE=../../../src/goto-harness/goto-harness
CBMC_EXE=../../../src/cbmc/cbmc
GOTO_CC_EXE=../../../src/goto-cc/goto-cc

ifeq ($(BUILD_ENV_),MSVC)
	is_windows=true
else
	is_windows=false
endif

test:
	@../test.pl -e -p -c "../chain.sh $(GOTO_CC_EXE) $(GOTO_HARNESS_EXE) $(MEMORY_ANALYZER_EXE) $(CBMC_EXE) $(is_windows)"

tests.log: ../test.pl
	@../test.pl -e -p -c "../chain.sh $(GOTO_CC_EXE) $(GOTO_HARNESS_EXE) $(MEMORY_ANALYZER_EXE) $(CBMC_EXE) $(is_windows)"

show:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			vim -o "$$dir/*.c" "$$dir/*.out"; \
		fi; \
	done;

clean:
	find -name '*.out' -execdir $(RM) '{}' \;
	find -name '*.gb' -execdir $(RM) '{}' \;
	find -name '*.json' -execdir $(RM) '{}' \;
	$(RM) tests.log
