all: build-test

CHARON_HOME=../charon/charon
CHARON_TESTS_DIR=$(CHARON_HOME)/tests/src
DEST_DIR=tests/

# Default translation options:
# - insert calls to the normalizer in the translated code to test the
#   generated unit functions
TRANS_OPTIONS:=-test-trans-units

# Build the project and test it
.PHONY: build-test
build-test: build test

# Build the project
.PHONY: build
build:
	dune build src/main.exe

# Test the project
.PHONY: test
test: build translate-no_nested_borrows translate-hashmap

# Add specific options to some tests
translate-no_nested_borrows: TRANS_OPTIONS:=$(TRANS_OPTIONS) -test-units -no-decrease-clauses
translate-hashmap: TRANS_OPTIONS:=$(TRANS_OPTIONS) -template-clauses

# Generic rule to extract the CFIM from a rust file
.PHONY: gen-cfim-%
gen-cfim-%: build
	cd ../charon/charon && cargo run tests/src/$*.rs

# Generic rule to test the translation on a CFIM file
.PHONY: translate-%
translate-%: gen-cfim-%
	dune exec -- src/main.exe $(CHARON_TESTS_DIR)/$*.cfim -dest $(DEST_DIR) $(TRANS_OPTIONS)

.PHONY: doc
doc:
	dune build @doc
