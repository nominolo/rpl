all: build

include config.mk

# If not set in custom config.mk, use the inplace GHC
HC            ?= ghc
PKG           ?= ghc-pkg
HADDOCK       ?= haddock
CABAL_INSTALL ?= cabal

DIST          ?= dist
SETUP_DIST    ?= setup-dist
SETUP_CONFIG  ?= $(DIST)/setup-config
SETUP         ?= $(SETUP_DIST)/Setup

CABAL_INSTALL_OPTS += --ghc --with-compiler=$(HC) --with-hc-pkg=$(PKG)
CABAL_FLAGS   ?= 

setup: $(SETUP)
$(SETUP): Setup.hs
	@mkdir -p $(SETUP_DIST)
	$(HC) --make -odir $(SETUP_DIST) -hidir $(SETUP_DIST) -o $@ $<

configure: $(SETUP_CONFIG)
$(SETUP_CONFIG): rpl.cabal $(SETUP)
	$(SETUP) configure -v --with-compiler=$(HC) --with-hc-pkg=$(PKG) --user $(CABAL_FLAGS)

.PHONY: build
build: configure
	$(SETUP) build -v

install: build
	$(SETUP) install

clean:
	$(SETUP) clean || rm -rf $(DIST)

distclean: clean
	rm -rf $(SETUP_DIST)

doc:
	$(SETUP) haddock --with-haddock=$(HADDOCK)

printvars:
	@echo "GHC_PATH         = $(GHC_PATH)"
	@echo "HC               = $(HC)"
	@echo "PKG              = $(PKG)"
	@echo "HADDOCK          = $(HADDOCK)"
	@echo "CABAL_INSTALL    = $(CABAL_INSTALL)"
	@echo "        ..._OPTS = $(CABAL_INSTALL_OPTS)"
	@echo "CABAL_FLAGS      = $(CABAL_FLAGS)"
	@echo "---------------------------------------------------------------"
	@echo "DIST         = $(DIST)"
	@echo "SETUP_CONFIG = $(SETUP_CONFIG)"
	@echo "SETUP_DIST   = $(SETUP_DIST)"

cabal-install:
	$(CABAL_INSTALL) install $(CABAL_INSTALL_OPTS) $(CABAL_FLAGS)
