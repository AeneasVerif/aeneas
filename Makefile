all: build-run

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
	dune exec -- src/main.exe $(CFIM_TEST_FILE1) -dest $(DEST_DIR) -test-units -test-trans-units
	dune exec -- src/main.exe $(CFIM_TEST_FILE2) -dest $(DEST_DIR) -test-trans-units

.PHONY: generate-cfim
generate-cfim:
	cd ../charon/charon && cargo run $(RS_TEST_FILE1)
	cd ../charon/charon && cargo run $(RS_TEST_FILE2)

doc:
	dune build @doc
