default: all

# include config.mk

exeext =

# If not set in custom config.mk, use the inplace GHC
HC            ?= ghc
PKG           ?= ghc-pkg
HADDOCK       ?= haddock
CABAL_INSTALL ?= cabal

DIST          = dist
SETUP_DIST    = setup-dist
SETUP         = $(SETUP_DIST)/Setup$(exeext)
SETUP_CONFIG  = $(DIST)/setup-config

CABAL_INSTALL_OPTS += --ghc --with-compiler=$(HC) --with-hc-pkg=$(PKG)
CABAL_FLAGS   ?= 

BUILD_DIRS = utils/
# SHELL = /usr/sh

MKDIRHIER = utils/mkdirhier/mkdirhier

RM = rm

# include $(patsubst %, %/local.mk, $(BUILD_DIRS))

########################################################################

$(SETUP): Setup.hs
	@echo === Building Setup program ===============================
	@mkdir -p $(SETUP_DIST)
	@ghc --make -odir $(SETUP_DIST) -hidir $(SETUP_DIST) -o $@ $<

$(DIST)/lib/setup-config: $(SETUP) lib/rpl.cabal
	@echo === Configuring library ==================================
	@cd lib && \
	../$(SETUP) configure --with-compiler=$(HC) --with-hc-pkg=$(PKG) \
		--user --builddir=../$(DIST)/lib $(CABAL_FLAGS)

$(DIST)/lib/build/libHSrpl-0.1.a: $(DIST)/lib/setup-config \
                                  lib/**/*.hs lib/**/*.x lib/**/*.y \
	                          lib/**/**/*.hs lib/**/**/**/*.hs
	@echo === Building library =====================================
	@cd lib && \
	../$(SETUP) build --builddir=../$(DIST)/lib $(CABAL_FLAGS)

$(DIST)/lib-pkg-conf: $(DIST)/lib/build/libHSrpl-0.1.a
	@echo === Registering library ==================================
	@cd lib && \
	../$(SETUP) register --builddir=../$(DIST)/lib --inplace # --gen-pkg-config=../$@
	@touch $@

$(DIST)/rplc/setup-config: $(SETUP) $(DIST)/lib-pkg-conf rplc/rplc.cabal
	@echo === Configuring rplc =====================================
	@cd rplc && \
	../$(SETUP) configure --with-compiler=$(HC) --with-hc-pkg=$(PKG) \
		--user --builddir=../$(DIST)/rplc $(CABAL_FLAGS)
$(DIST)/rplc/build/rplc/rplc: $(DIST)/rplc/setup-config
	@echo === Building rplc ========================================
	@cd rplc && \
	../$(SETUP) build --builddir=../$(DIST)/rplc $(CABAL_FLAGS)

$(DIST)/testsuite/setup-config: $(SETUP) $(DIST)/lib-pkg-conf testsuite/rpl-testsuite.cabal
	@echo === Configuring testsuite ================================
	@cd testsuite && \
	../$(SETUP) configure --with-compiler=$(HC) --with-hc-pkg=$(PKG) \
		--user --builddir=../$(DIST)/testsuite $(CABAL_FLAGS)
$(DIST)/testsuite/build/rpl-testsuite/rpl-testsuite: $(DIST)/testsuite/setup-config testsuite/RPL/**/*.hs
	@echo === Building testsuite ===================================
	@cd testsuite && \
	../$(SETUP) build --builddir=../$(DIST)/testsuite $(CABAL_FLAGS)

.PHONY: clean all lib comp suite test

all: comp suite
lib: $(DIST)/lib/build/libHSrpl-0.1.a
comp: $(DIST)/rplc/build/rplc/rplc
suite: $(DIST)/testsuite/build/rpl-testsuite/rpl-testsuite
test: suite
	@./$(DIST)/testsuite/build/rpl-testsuite/rpl-testsuite

clean:
	@$(RM) -rf $(SETUP_DIST) $(DIST)

########################################################################

# lib_dist_HS_SRCS = lib/RPL/Typecheck/AlgorithmW.hs

# lib_dist_depfile = dist/lib/build/.depend

# $(lib_dist_depfile) : $(lib_dist_HS_SRCS)
# 	mkdir -p dist/lib/build
# 	$(RM) $@ $@.tmp
# 	touch $@.tmp
# 	ghc -M -dep-makefile $@ -ilib -odist/lib/build $(lib_dist_HS_SRCS)
# 	echo "lib_dist_depfile_EXISTS = YES" >> $@

# all: $(lib_dist_depfile)

########################################################################

# define build-dependencies # args: $1 = dir, $2 = distdir

# $1_$2_MKDEPENDHS_FLAGS = -include-pkg-deps -dep-makefile $$($1_$2_depfile) $$(foreach way,$$(filter-out v,$$($1_$2_WAYS)),-dep-suffix $$(way))

# $$($1_$2_depfile) : $$(MKDIRHIER) $$(MKDEPENDC) $$($1_$2_HS_SRCS) $$($1_$2_HS_BOOT_SRCS) $$($1_$2_HC_MK_DEPEND_DEP) $$($1_$2_C_FILES) $$($1_$2_S_FILES)
# 	$$(MKDIRHIER) $1/$2/build
# 	$$(RM) $$@ $$@.tmp
# 	touch $$@.tmp
# ifneq "$$($1_$2_HS_SRCS)" ""
# 	$$($1_$2_HC_MK_DEPEND) -M $$($1_$2_MKDEPENDHS_FLAGS) \
# 	    $$(filter-out -split-objs, $$($1_$2_v_ALL_HC_OPTS)) \
# 	    $$($1_$2_HS_SRCS) || ( $$(RM) $$@; exit 1 )
# endif
# 	echo "$1_$2_depfile_EXISTS = YES" >> $$@
# endef

########################################################################

# define build-prog
# # $1 = dir
# # $2 = distdir

# $1_$2_depfile = $1/$2/build/.depend

# $(call build-dependencies,$1,$2)

# endef

########################################################################

# $(eval $(call build-prog,utils/hpc,dist))

# .PHONY: build
# build: $(SETUP_CONFIG)
# 	$(SETUP) build -v

# install: build
# 	$(SETUP) install

# clean:
# 	$(SETUP) clean || rm -rf $(DIST)

# distclean: clean
# 	rm -rf $(SETUP_DIST)

# doc:
# 	$(SETUP) haddock --with-haddock=$(HADDOCK)

# printvars:
# 	@echo "GHC_PATH         = $(GHC_PATH)"
# 	@echo "HC               = $(HC)"
# 	@echo "PKG              = $(PKG)"
# 	@echo "HADDOCK          = $(HADDOCK)"
# 	@echo "CABAL_INSTALL    = $(CABAL_INSTALL)"
# 	@echo "        ..._OPTS = $(CABAL_INSTALL_OPTS)"
# 	@echo "CABAL_FLAGS      = $(CABAL_FLAGS)"
# 	@echo "---------------------------------------------------------------"
# 	@echo "DIST         = $(DIST)"
# 	@echo "SETUP_CONFIG = $(SETUP_CONFIG)"
# 	@echo "SETUP_DIST   = $(SETUP_DIST)"

# cabal-install:
# 	$(CABAL_INSTALL) install $(CABAL_INSTALL_OPTS) $(CABAL_FLAGS)
