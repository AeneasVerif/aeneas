all: build-run-check-trace

CHARON_HOME=../charon/charon
CHARON_TESTS_DIR=$(CHARON_HOME)/tests/src
DEST_DIR=tests/

RS_TEST_FILE1=tests/src/no_nested_borrows.rs
CFIM_TEST_FILE1=$(CHARON_TESTS_DIR)/no_nested_borrows.cfim

RS_TEST_FILE2=tests/src/hashmap.rs
CFIM_TEST_FILE2=$(CHARON_TESTS_DIR)/hashmap.cfim

# Build the project
.PHONY: build
build:
	dune build src/main.exe

# Build the project and run the executable
.PHONY: build-run
build-run: build
	dune exec -- src/main.exe $(CFIM_TEST_FILE1) -dest $(DEST_DIR) -test-units -test-trans-units > tests/trace_current.txt
	dune exec -- src/main.exe $(CFIM_TEST_FILE2) -dest $(DEST_DIR) -test-trans-units

# Build the project and run the executable, then check that the behaviour
# of the interpreter didn't change by comparing the newly generated trace
# with a reference.
.PHONY: build-run-check-trace
build-run-check-trace: generate-cfim build-run
	cmp tests/trace_reference.txt tests/trace_current.txt && \
	cp fstar/Primitives.fst $(DEST_DIR)

# Build the project and update the trace
.PHONY: regen-trace
regen-trace: generate-cfim build-run
	rm -f tests/trace_reference.txt && \
	cp tests/trace_current.txt tests/trace_reference.txt && \
	cp fstar/Primitives.fst $(DEST_DIR)

.PHONY: generate-cfim
generate-cfim:
	cd ../charon/charon && cargo run $(RS_TEST_FILE1)
	cd ../charon/charon && cargo run $(RS_TEST_FILE2)

doc:
	dune build @doc
