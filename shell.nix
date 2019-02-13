with import <mathcomp> {};

stdenv.mkDerivation rec {
  name = "env";
  env = buildEnv { name = name; paths = buildInputs; };
  buildInputs = [ coq_8_8 ]
    ++ (with coqPackages; [ mathcomp paramcoq ]);
}
