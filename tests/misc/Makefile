INCLUDE_DIRS = .

FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDE_DIRS))

FSTAR_HINTS ?= --use_hints --use_hint_hashes --record_hints

FSTAR_OPTIONS = $(FSTAR_HINTS) \
  --odir obj --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --warn_error '+241@247+285-274' \
  --cache_dir obj

FSTAR_NO_FLAGS = fstar.exe

FSTAR = $(FSTAR_NO_FLAGS) $(FSTAR_OPTIONS)

# The F* roots are used to compute the dependency graph, and generate the .depend file
FSTAR_ROOTS ?= $(wildcard *.fst *.fsti)

# This is the right way to ensure the .depend file always gets re-built.
ifeq (,$(filter %-in,$(MAKECMDGOALS)))
ifndef NODEPEND
ifndef MAKE_RESTARTS
.depend: .FORCE
	$(FSTAR_NO_FLAGS) --dep full $(notdir $(FSTAR_ROOTS)) > $@

.PHONY: .FORCE
.FORCE:
endif
endif

include .depend
endif

# For the interactive mode
%.fst %.fsti:
	$(FSTAR) $@

# Generete the .checked files in bash mode
%.checked:
	$(FSTAR) $(FSTAR_FLAGS) $* && \
	touch -c $*

# Build all the files
all: $(ALL_CHECKED_FILES)

.PHONY: clean
clean:
	rm -f obj/*
