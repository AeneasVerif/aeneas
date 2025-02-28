ALL_DIRS ?= $(filter-out %~ lean-toolchain% Makefile%, $(wildcard *))

# TODO: remove
UPDATE_DIRS = $(addprefix update-,$(ALL_DIRS))

# TODO: remove
VERIFY_DIRS = $(addprefix verif-,$(ALL_DIRS))

# TODO: remove
CLEAN_DIRS = $(addprefix clean-,$(ALL_DIRS))

# TODO: remove
COPY_LEAN_TOOLCHAIN = $(addprefix copy-lean-toolchain-,$(ALL_DIRS))

.PHONY: all
all: prepare-projects verify

.PHONY: prepare-projects
prepare-projects: copy-lean-toolchain lakefile.lean

.PHONY: copy-lean-toolchain
copy-lean-toolchain:
	cp ../../backends/lean/lean-toolchain .

.PHONY: lakefile.lean
lakefile.lean:
	bash script.sh

.PHONY: update
update:
	lake update

.PHONY: verify
verify:
	lake build

.PHONY: clean
clean:
	lake clean
