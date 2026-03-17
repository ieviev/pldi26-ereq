{
  description = "EREQ dev-shell with MONA and Rust nightly";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    rust-overlay = {
      url = "github:oxalica/rust-overlay";
      inputs.nixpkgs.follows = "nixpkgs";
    };
    mona-src = {
      url = "github:cs-au-dk/MONA/e10403bf9d193a0e490ce735bb5514263a00165b";
      flake = false;
    };
  };

  outputs =
    { self, nixpkgs, rust-overlay, mona-src }:
    let
      system = "x86_64-linux";
      pkgs = import nixpkgs {
        inherit system;
        overlays = [ rust-overlay.overlays.default ];
      };
      rust-nightly = pkgs.rust-bin.nightly.latest.default;
      mona = pkgs.stdenv.mkDerivation {
        pname = "mona";
        version = "1.4";
        src = mona-src;

        nativeBuildInputs = with pkgs; [
          autoreconfHook
          bison
          flex
          libtool
        ];

        meta = {
          description = "MONA - MSO/WS1S/WS2S decision procedure";
          platforms = pkgs.lib.platforms.linux;
        };
      };
      mona-limited = pkgs.writeShellScriptBin "mona-limited" ''
        ulimit -v "''${MONA_MEM_LIMIT_KB:-16777216}"
        exec ${mona}/bin/mona "$@"
      '';
    in
    {
      packages.${system} = { mona = mona; mona-limited = mona-limited; default = mona; };
      devShells.${system}.default = pkgs.mkShell {
        packages = [
          rust-nightly
          mona
          mona-limited
          pkgs.nodejs
          pkgs.jq
        ];
      };
    };
}
