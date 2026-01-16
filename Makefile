SRC_DIRS := 'src'
PROJ_VFILES := $(shell fd -I -H -e v -E '*__nobuild.v' . $(SRC_DIRS))
GOOSE_CONFIG_FILES := $(shell fd -I -H -e "v.toml" -E '*__nobuild.v' . src)
GO_DIR := 'hashtriemap'
GO_FILES := $(shell find $(GO_DIR) -name "*.go")

# extract any global arguments for Rocq from _RocqProject
ROCQPROJECT_ARGS := $(shell sed -E -e '/^\#/d' -e "s/'([^']*)'/\1/g" -e 's/-arg //g' _RocqProject)

# user configurable
Q:=@
ROCQ_ARGS :=
ROCQC := rocq compile
ROCQ_DEP_ARGS := -w +module-not-found

default: vo
.PHONY: default

vo: $(PROJ_VFILES:.v=.vo)
vos: $(PROJ_VFILES:.v=.vos)
vok: $(PROJ_VFILES:.v=.vok)

.goose-output: $(GO_FILES) $(GOOSE_CONFIG_FILES) goose.toml
	@echo "GOOSE"
	$(Q)perennial-cli goose
	@touch $@

# UNCOMMENT THIS SECTION (AND COMMENT OUT THE NEXT ONE) IF YOU DONT HAVE XONSH INSTALLED
# .rocqdeps.d: $(PROJ_VFILES) _RocqProject .goose-output
# 	@echo "ROCQ dep $@"
# 	$(Q)rocq dep $(ROCQ_DEP_ARGS) -vos -f _RocqProject $(PROJ_VFILES) > $@

.rocqdeps.d: $(PROJ_VFILES) _RocqProject .goose-output
	@echo "ROCQ dep $@"
	$(Q)./build_deps.xsh $(ROCQ_DEP_ARGS) -vos -f _RocqProject -- $(PROJ_VFILES) > $@

# do not try to build dependencies if cleaning
ifeq ($(filter clean,$(MAKECMDGOALS)),)
-include .rocqdeps.d
endif

%.vo: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ compile $<"
	$(Q)$(ROCQC) $(ROCQPROJECT_ARGS) $(ROCQ_ARGS) -o $@ $<

%.vos: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ -vos $<"
	$(Q)$(ROCQC) $(ROCQPROJECT_ARGS) -vos $(ROCQ_ARGS) $< -o $@

%.vok: %.v _RocqProject | .rocqdeps.d
	@echo "ROCQ -vok $<"
	$(Q)$(ROCQC) $(ROCQPROJECT_ARGS) -vok $(ROCQ_ARGS) $< -o $@

clean:
	@echo "CLEAN vo glob aux"
	$(Q)find $(SRC_DIR) \( -name "*.vo" -o -name "*.vo[sk]" \
		-o -name ".*.aux" -o -name ".*.cache" -o -name "*.glob" \) -delete
	$(Q)for dir in $(SRC_DIR)/code $(SRC_DIR)/generatedproof; do \
		if test -d "$$dir"; then find "$$dir" -name "*.v" -delete; fi \
	done
	$(Q)rm -f .goose-output
	$(Q)rm -f .rocqdeps.d

.PHONY: default
.DELETE_ON_ERROR:
