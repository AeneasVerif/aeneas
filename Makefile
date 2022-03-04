all: build-test

CHARON_HOME = ../charon
CHARON_EXEC = $(CHARON_HOME)/charon
DEST_DIR = tests

# We use those variables, whose definition depends on the rule we apply
CHARON_TESTS_DIR =
CHARON_OPTIONS =
CHARON_TESTS_SRC =

# The user can specify additional translation options for Aeneas:
OPTIONS ?=

# Default translation options:
# - insert calls to the normalizer in the translated code to test the
#   generated unit functions
TRANS_OPTIONS := -test-trans-units $(OPTIONS)
SUBDIR :=

# Build the project and test it
.PHONY: build-test
build-test: build test

# Build the project
.PHONY: build
build:
	dune build src/main.exe

# Test the project
.PHONY: test
test: build translate-no_nested_borrows translate-hashmap translate-paper \
	translate-external translate-nll-betree_nll

# Add specific options to some tests
translate-no_nested_borrows translate-paper: \
	TRANS_OPTIONS += -test-units -no-split-files -no-state -no-decreases-clauses
translate-no_nested_borrows translate-paper: SUBDIR:=misc
translate-hashmap: TRANS_OPTIONS += -template-clauses -no-state
translate-hashmap: SUBDIR:=hashmap

translate-nll-betree_nll: TRANS_OPTIONS += -test-units -no-split-files -no-state -no-decreases-clauses
translate-nll-betree_nll: SUBDIR:=misc

translate-external: TRANS_OPTIONS +=
translate-external: SUBDIR:=misc

# Generic rules to extract the LLBC from a rust file
# We use the rules in Charon's Makefile to generate the .llbc files: the options
# vary with the test files.
.PHONY: gen-llbc-%
gen-llbc-%: build
	cd $(CHARON_HOME) && make test-$*

# Generic rule to test the translation on an LLBC file.
# Note that the non-linear lifetime files are generated in the tests-nll
# subdirectory.
.PHONY: translate-%
translate-%: CHARON_TESTS_DIR = $(CHARON_HOME)/tests/llbc
translate-nll-%: CHARON_TESTS_DIR = $(CHARON_HOME)/tests-nll/llbc

translate-%: gen-llbc-%
	dune exec -- src/main.exe $(CHARON_TESTS_DIR)/$*.llbc -dest $(DEST_DIR)/$(SUBDIR) $(TRANS_OPTIONS)

translate-nll-%: gen-llbc-nll-%
	dune exec -- src/main.exe $(CHARON_TESTS_DIR)/$*.llbc -dest $(DEST_DIR)/$(SUBDIR) $(TRANS_OPTIONS)

.PHONY: doc
doc:
	dune build @doc
