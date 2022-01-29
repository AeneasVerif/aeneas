all: build-run-check-trace

CHARON_HOME=../charon/charon
CHARON_TESTS_DIR=$(CHARON_HOME)/tests
RS_TEST_FILE=tests/no_nested_borrows.rs
CFIM_TEST_FILE=$(CHARON_TESTS_DIR)/no_nested_borrows.cfim

# Build the project and run the executable
.PHONY: build-run
build-run:
	dune build src/main.exe && dune exec src/main.exe

# Build the project and run the executable, then check that the behaviour
# of the interpreter didn't change by comparing the newly generated trace
# with a reference.
.PHONY: build-run-check-trace
build-run-check-trace: generate-cfim
	dune build src/main.exe && \
	dune exec src/main.exe $(CFIM_TEST_FILE) > tests/trace_current.txt && \
	cmp tests/trace_reference.txt tests/trace_current.txt

# Build the project and update the trace
.PHONY: regen-trace
regen-trace: generate-cfim
	dune build src/main.exe && \
	dune exec src/main.exe $(CFIM_TEST_FILE) > tests/trace_current.txt && \
        rm -f tests/trace_reference.txt && \
	cp tests/trace_current.txt tests/trace_reference.txt

.PHONY: generate-cfim
generate-cfim:
	cd ../charon/charon && cargo run $(RS_TEST_FILE)

doc:
	dune build @doc
