{ fetchFromGitHub
, mkCoqDerivation
}: let
  src = fetchFromGitHub {
    owner = "charguer";
    repo = "tlc";
    rev = "fd53b3b2f0a0d7c24c8363fbd4570a451198ded7";
    hash = "sha256-NmOGykMUUdWgaHzbJGXP+DP5KM0XlomvzL8Wnn1/FkE=";
  };
in mkCoqDerivation {
  pname = "tlc";
  version = "20250523";
  inherit src;
}
