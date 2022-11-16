ALL_DIRS ?= $(filter-out Makefile%, $(wildcard *))

VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

COPY_MAKEFILES = $(addprefix copy-makefile-,$(ALL_DIRS))

.PHONY: all
all: $(COPY_MAKEFILES) $(VERIFY_DIRS)

.PHONY: clean
clean: $(CLEAN_DIRS)

.PHONY: verif-%
verif-%:
	cd $* && make all

.PHONY: copy-makefile-%
copy-makefile-%:
	rm -f $*/Makefile
	echo "# This file was automatically generated - modify ../Makefile.template instead" >> $*/Makefile
	cat Makefile.template >> $*/Makefile

.PHONY: clean-%
clean-%:
	cd $* && make clean
