ALL_DIRS ?= $(filter-out Makefile%, $(wildcard *))

VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

.PHONY: all
all: $(VERIFY_DIRS)

.PHONY: clean
clean: $(CLEAN_DIRS)

.PHONY: verif-%
verif-%:
	cd $* && make all

.PHONY: clean-%
clean-%:
	cd $* && make clean
