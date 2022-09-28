ifeq (3.81,$(MAKE_VERSION))
  $(error You seem to be using the OSX antiquated Make version. Hint: brew \
    install make, then invoke gmake instead of make)
endif



all: build-test-verify

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

# Build the project, test it and verify the generated files
.PHONY: build-test-verify
build-test-verify: build test verify

# Check the OCaml version
.PHONY: check-ocaml
check-ocaml:
	bash check_ocaml

# Build the project
.PHONY: build
build: check-ocaml
	dune build src/main.exe

# Test the project by translating test files to F*
.PHONY: test
test: build trans-no_nested_borrows trans-paper \
	trans-hashmap trans-hashmap_main \
	trans-external trans-constants \
	trans-nll-betree_nll trans-nll-betree_main

# Verify the F* files generated by the translation
.PHONY: verify
verify: build test
	cd tests && $(MAKE) all

# Reformat the project
.PHONY: format
format:
	dune build @fmt && dune promote

# Add specific options to some tests
trans-no_nested_borrows trans-paper: \
	TRANS_OPTIONS += -test-units -no-split-files -no-state -no-decreases-clauses
trans-no_nested_borrows trans-paper: SUBDIR:=misc

trans-hashmap: TRANS_OPTIONS += -template-clauses -no-state
trans-hashmap: SUBDIR:=hashmap

trans-hashmap_main: TRANS_OPTIONS += -template-clauses
trans-hashmap_main: SUBDIR:=hashmap_on_disk

trans-nll-betree_nll: TRANS_OPTIONS += -test-units -no-split-files -no-state -no-decreases-clauses
trans-nll-betree_nll: SUBDIR:=misc

trans-constants: TRANS_OPTIONS += -test-units -no-split-files -no-state -no-decreases-clauses
trans-constants: SUBDIR:=misc

trans-external: TRANS_OPTIONS +=
trans-external: SUBDIR:=misc

trans-nll-betree_main: TRANS_OPTIONS += -template-clauses
trans-nll-betree_main: SUBDIR:=betree

# Generic rules to extract the LLBC from a rust file
# We use the rules in Charon's Makefile to generate the .llbc files: the options
# vary with the test files.
.PHONY: gen-llbc-%
gen-llbc-%: build
	cd $(CHARON_HOME) && $(MAKE) test-$*

# Generic rule to test the translation of an LLBC file.
# Note that the non-linear lifetime files are generated in the tests-nll subdirectory.
.PHONY: trans-%
trans-%: CHARON_TESTS_DIR = $(CHARON_HOME)/tests/llbc
trans-nll-%: CHARON_TESTS_DIR = $(CHARON_HOME)/tests-nll/llbc

trans-%: gen-llbc-%
	dune exec -- src/main.exe $(CHARON_TESTS_DIR)/$*.llbc -dest $(DEST_DIR)/$(SUBDIR) $(TRANS_OPTIONS)

trans-nll-%: gen-llbc-nll-%
	dune exec -- src/main.exe $(CHARON_TESTS_DIR)/$*.llbc -dest $(DEST_DIR)/$(SUBDIR) $(TRANS_OPTIONS)

.PHONY: doc
doc:
	dune build @doc
