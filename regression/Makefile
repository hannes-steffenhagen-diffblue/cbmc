# For the best possible utilisation of multiple cores when
# running tests in parallel, it is important that these directories are
# listed with decreasing runtimes (i.e. longest running at the top)
DIRS = cbmc \
       ansi-c \
       cbmc-concurrency \
       cbmc-cover \
       cbmc-cpp \
       cbmc-incr-oneloop \
       cbmc-library \
       contracts \
       cpp \
       goto-analyzer \
       goto-analyzer-taint \
       goto-cc-cbmc \
       goto-cc-file-local \
       goto-cc-goto-analyzer \
       goto-cl \
       goto-diff \
       goto-gcc \
       goto-harness \
       goto-instrument \
       goto-instrument-typedef \
       invariants \
       linking-goto-binaries \
       smt2_solver \
       smt2_strings \
       solver-hardness \
       statement-list \
       strings \
       symtab2gb \
       systemc \
       test-script \
       validate-trace-xml-schema \
       # Empty last line

ifeq ($(OS),Windows_NT)
    detected_OS := Windows
else
    detected_OS := $(shell sh -c 'uname 2>/dev/null || echo Unknown')
endif

ifeq ($(detected_OS),Linux)
  ifneq ($(WITH_MEMORY_ANALYZER),0)
    # only set if it wasn't explicitly unset
    WITH_MEMORY_ANALYZER=1
  endif
endif

ifeq ($(WITH_MEMORY_ANALYZER),1)
  DIRS += snapshot-harness \
          memory-analyzer
endif

# Run all test directories in sequence
.PHONY: test
test:
	@for dir in $(DIRS); do \
		$(MAKE) "$$dir" || exit 1; \
	done;

# Pattern to execute a single test suite directory
.PHONY: $(DIRS)
$(DIRS):
	@echo "Running $@..." ;
	$(MAKE) -C "$@" test || exit 1;

# Run all test directories using GNU Parallel
.PHONY: test-parallel
.NOTPARALLEL: test-parallel
test-parallel:
	@echo "Building with $(JOBS) jobs"
	parallel \
		--halt soon,fail=1 \
		--tag \
		--tagstring '{#}:' \
		--linebuffer \
		--jobs $(JOBS) \
		$(MAKE) "{}" \
		::: $(DIRS)


.PHONY: clean
clean:
	@for dir in *; do \
		if [ -d "$$dir" ]; then \
			$(MAKE) -C "$$dir" clean; \
		fi; \
	done;
