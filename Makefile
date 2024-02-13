all: prop type

install: prop_install type_install

prop:
	export TIMED
	cp -f theories/implem/prop.v theories/base/base_implem.v
	rm -f theories/_CoqProject
	echo '-R . KruskalAfProp' > theories/_CoqProject
	cat theories/CoqProject >> theories/_CoqProject
#	cp -f theories/CoqProjectProp theories/_CoqProject
	@+$(MAKE) -C theories Makefile
	@+$(MAKE) -C theories clean
	@+$(MAKE) -C theories all

type:
	export TIMED
	cp -f theories/implem/type.v theories/base/base_implem.v
	rm -f theories/_CoqProject
	echo '-R . KruskalAfType' > theories/_CoqProject
	cat theories/CoqProject >> theories/_CoqProject
#	cp -f theories/CoqProjectType theories/_CoqProject
	@+$(MAKE) -C theories Makefile
	@+$(MAKE) -C theories clean
	@+$(MAKE) -C theories all

prop_install: prop
	@+$(MAKE) -C theories install

type_install: type
	@+$(MAKE) -C theories install

force Makefile: ;

.PHONY: force
