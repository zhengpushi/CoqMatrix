Copyright
```text
Copyright 2022 ZhengPu Shi
  This file is part of CoqExt. It is distributed under the MIT
  "expat license". You should have recieved a LICENSE file with it.
```

# CoqExt
Extension for Coq stdandard library.
https://github.com/zhengpushi/CoqExt


## 1. Introduction
This is a submodule of [VFCS](https://github.com/zhengpushi/VFCS) project.
But, it could be free used by anybody who need it, and only thing is abey the MIT license.

purpose   : 
1. Extension of number type in coq standard libray
2. Mathematical hierarchy, setoid version
3. List extension, setoid version
4. other extensions.

## 2. Files list
* BasicConfig.v : depended libraries, reserved notations, default scopes.
* BoolExt.v : boolean extension
* ExtrOcamlR.v : extension for extraction R type
* FuncExt.v : function extension
* Hierarchy_ModuleType.v : math hierarchy implemented with module type (not use)
* HierarchySetoid.v : math hierarchy implemented with typeclass, setoid version.
* NatExt.v : nat extension
* QcExt.v : Qc extension
* QExt.v : Q extension
* RExt.v : R extension
* RAST.v : Abstract Syntax Tree of R, simple implementation
* SetoidListExt.v : list extension, setoid version
* SetoidListListExt.v : list list extension, setoid version
* StrExt.v : string extension
* TupleExt.v : tuple extension
* ZExt.v : Z extension
