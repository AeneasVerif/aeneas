INCLUDE_DIRS = .

FSTAR_INCLUDES = $(addprefix --include ,$(INCLUDE_DIRS))

FSTAR_HINTS ?= --use_hints --use_hint_hashes --record_hints

FSTAR_OPTIONS = $(FSTAR_HINTS) \
  --cache_checked_modules $(FSTAR_INCLUDES) --cmi \
  --warn_error '+241@247+285-274' \

FSTAR_NO_FLAGS = fstar.exe --already_cached 'Prims FStar LowStar Steel' --odir obj --cache_dir obj

FSTAR = $(FSTAR_NO_FLAGS) $(FSTAR_OPTIONS)

# The F* roots are used to compute the dependency graph, and generate the .depend file
FSTAR_ROOTS ?= $(wildcard *.fst *.fsti)

# Build all the files
all: $(addprefix obj/,$(addsuffix .checked,$(FSTAR_ROOTS)))

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
%.fst-in %.fsti-in:
	@echo $(FSTAR_OPTIONS)

# Generete the .checked files in batch mode
%.checked:
	$(FSTAR) $(FSTAR_OPTIONS) $< && \
	touch -c $@

.PHONY: clean
clean:
	rm -f obj/*
