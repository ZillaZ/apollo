# To learn more about how to use Nix to configure your environment
# see: https://firebase.google.com/docs/stulsdio/customize-workspace
{ pkgs, ... }: {
  # Which nixpkgs channel to use.
  channel = "stable-24.05"; # or "unstable"

  # Use https://search.nixos.org/packages to find packages
  packages = with pkgs; [
    clang
    llvmPackages.bintools
    rustup
    gcc
    libgccjit
    libgcc
    nix-ld
  ];

  # Sets environment variables in the workspace
  env = {
    RUSTC_VERSION = "stable";
    APOLLO_LIBS = "/home/user/apollo/libs";
    APOLLO_CORE = "/home/user/apollo/core";
  };
  idx = {
    # Search for the extensions you want on https://open-vsx.org/ and use "publisher.id"
    extensions = [
      "rust-lang.rust-analyzer"
    ];

    # Enable previews
    previews = {
      enable = true;
      previews = {
        # web = {
        #   # Example: run "npm run dev" with PORT set to IDX's defined port for previews,
        #   # and show it in IDX's web preview panel
        #   command = ["npm" "run" "dev"];
        #   manager = "web";
        #   env = {
        #     # Environment variables to set for your server
        #     PORT = "$PORT";
        #   };
        # };
      };
    };

    # Workspace lifecycle hooks
    workspace = {
      # Runs when a workspace is first created
      onCreate = {
        # Example: install JS dependencies from NPM
        # npm-install = "npm install";
        export_ld = "export LD_LIBRARY_PATH=\"/lib\"";
        export = "export LIBRARY_PATH=\"/lib\"";
      };
      # Runs when the workspace is (re)started
      onStart = {
        # Example: start a background task to watch and re-build backend code
        # watch-backend = "npm run watch-backend";
      };
    };
  };
}
