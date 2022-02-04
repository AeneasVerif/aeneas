all: build-run-check-trace

CHARON_HOME=../charon/charon
CHARON_TESTS_DIR=$(CHARON_HOME)/tests
RS_TEST_FILE=tests/no_nested_borrows.rs
CFIM_TEST_FILE=$(CHARON_TESTS_DIR)/no_nested_borrows.cfim
DEST_DIR=tests/

# Build the project
.PHONY: build
build:
	dune build src/main.exe

# Build the project and run the executable
.PHONY: build-run
build-run: build
	dune exec -- src/main.exe $(CFIM_TEST_FILE) -dest $(DEST_DIR) > tests/trace_current.txt

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
	cd ../charon/charon && cargo run $(RS_TEST_FILE)

doc:
	dune build @doc
