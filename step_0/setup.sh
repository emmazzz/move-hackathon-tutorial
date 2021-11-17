Z3_VERSION=4.8.9
DOTNET_VERSION=5.0
BOOGIE_VERSION=2.9.6
INSTALL_DIR="${HOME}/bin/"


function add_to_profile {
  eval "$1"
  FOUND=$(grep -c "$1" < "${HOME}/.profile" || true)  # grep error return would kill the script.
  if [ "$FOUND" == "0" ]; then
    echo "$1" >> "${HOME}"/.profile
  fi
}

function install_rustup {
  if [[ "$OPT_DIR" == "true" ]]; then
     export RUSTUP_HOME=/opt/rustup/
     mkdir -p "$RUSTUP_HOME" || true
     export CARGO_HOME=/opt/cargo/
     mkdir -p "$CARGO_HOME" || true
  fi

  # Install Rust
  echo "Installing Rust......"
  VERSION="$(rustup --version || true)"
  if [ -n "$VERSION" ]; then
    echo "Rustup is already installed, version: $VERSION"
  else
	  curl https://sh.rustup.rs -sSf | sh -s -- -y --default-toolchain stable
    if [[ -n "${CARGO_HOME}" ]]; then
      PATH="${CARGO_HOME}/bin:${PATH}"
    else
      PATH="${HOME}/.cargo/bin:${PATH}"
    fi
  fi
}

function install_z3 {
  echo "Installing Z3"
  if command -v /usr/local/bin/z3 &>/dev/null; then
    echo "z3 already exists at /usr/local/bin/z3"
    echo "but this install will go to ${INSTALL_DIR}/z3."
    echo "you may want to remove the shared instance to avoid version confusion"
  fi
  if command -v "${INSTALL_DIR}z3" &>/dev/null && [[ "$("${INSTALL_DIR}z3" --version || true)" =~ .*${Z3_VERSION}.* ]]; then
     echo "Z3 ${Z3_VERSION} already installed"
     return
  fi
  if [[ "$(uname)" == "Linux" ]]; then
    Z3_PKG="z3-$Z3_VERSION-x64-ubuntu-16.04"
  elif [[ "$(uname)" == "Darwin" ]]; then
    Z3_PKG="z3-$Z3_VERSION-x64-osx-10.14.6"
  else
    echo "Z3 support not configured for this platform (uname=$(uname))"
    return
  fi
  TMPFILE=$(mktemp)
  rm "$TMPFILE"
  mkdir -p "$TMPFILE"/
  (
    cd "$TMPFILE" || exit
    curl -LOs "https://github.com/Z3Prover/z3/releases/download/z3-$Z3_VERSION/$Z3_PKG.zip"
    unzip -q "$Z3_PKG.zip"
    cp "$Z3_PKG/bin/z3" "${INSTALL_DIR}"
    chmod +x "${INSTALL_DIR}z3"
  )
  rm -rf "$TMPFILE"
}

function install_dotnet {
  echo "Installing .Net"
  mkdir -p "${DOTNET_INSTALL_DIR}" || true
  if [[ $("${DOTNET_INSTALL_DIR}/dotnet" --list-sdks | grep -c "^${DOTNET_VERSION}" || true) == "0" ]]; then
    if [[ "$(uname)" == "Linux" ]]; then
        # Install various prerequisites for .dotnet. There are known bugs
        # in the dotnet installer to warn even if they are present. We try
        # to install anyway based on the warnings the dotnet installer creates.
        if [ "$PACKAGE_MANAGER" == "apk" ]; then
          install_pkg icu "$PACKAGE_MANAGER"
          install_pkg zlib "$PACKAGE_MANAGER"
          install_pkg libintl "$PACKAGE_MANAGER"
          install_pkg libcurl "$PACKAGE_MANAGER"
        elif [ "$PACKAGE_MANAGER" == "apt-get" ]; then
          install_pkg gettext "$PACKAGE_MANAGER"
          install_pkg zlib1g "$PACKAGE_MANAGER"
        elif [ "$PACKAGE_MANAGER" == "yum" ] || [ "$PACKAGE_MANAGER" == "dnf" ]; then
          install_pkg icu "$PACKAGE_MANAGER"
          install_pkg zlib "$PACKAGE_MANAGER"
        elif [ "$PACKAGE_MANAGER" == "pacman" ]; then
          install_pkg icu "$PACKAGE_MANAGER"
          install_pkg zlib "$PACKAGE_MANAGER"
        fi
    fi
    # Below we need to (a) set TERM variable because the .net installer expects it and it is not set
    # in some environments (b) use bash not sh because the installer uses bash features.
    curl -sSL https://dot.net/v1/dotnet-install.sh \
        | TERM=linux /bin/bash -s -- --channel $DOTNET_VERSION --install-dir "${DOTNET_INSTALL_DIR}" --version latest
  else
    echo Dotnet already installed.
  fi
}

function install_boogie {
  echo "Installing boogie"
  mkdir -p "${DOTNET_INSTALL_DIR}tools/" || true
  if [[ "$("${DOTNET_INSTALL_DIR}dotnet" tool list --tool-path "${DOTNET_INSTALL_DIR}tools/")" =~ .*boogie.*${BOOGIE_VERSION}.* ]]; then
    echo "Boogie $BOOGIE_VERSION already installed"
  else
    "${DOTNET_INSTALL_DIR}dotnet" tool update --tool-path "${DOTNET_INSTALL_DIR}tools/" Boogie --version $BOOGIE_VERSION
  fi
}

function update_path_and_profile {
  touch "${HOME}"/.profile

  DOTNET_ROOT="$HOME/.dotnet"
  BIN_DIR="$HOME/bin"
  C_HOME="${HOME}/.cargo"
  if [[ "$OPT_DIR" == "true" ]]; then
    DOTNET_ROOT="/opt/dotnet"
    BIN_DIR="/opt/bin"
    C_HOME="/opt/cargo"
  fi

  mkdir -p "${BIN_DIR}"
  if [ -n "$CARGO_HOME" ]; then
    add_to_profile "export CARGO_HOME=\"${CARGO_HOME}\""
    add_to_profile "export PATH=\"${BIN_DIR}:${CARGO_HOME}/bin:\$PATH\""
  else
    add_to_profile "export PATH=\"${BIN_DIR}:${C_HOME}/bin:\$PATH\""
  fi
  add_to_profile "export DOTNET_ROOT=\"${DOTNET_ROOT}\""
  add_to_profile "export PATH=\"${DOTNET_ROOT}/tools:\$PATH\""
  add_to_profile "export Z3_EXE=\"${BIN_DIR}/z3\""
  add_to_profile "export BOOGIE_EXE=\"${DOTNET_ROOT}/tools/boogie\""
}

PACKAGE_MANAGER=
if [[ "$(uname)" == "Linux" ]]; then
	if command -v yum &> /dev/null; then
		PACKAGE_MANAGER="yum"
	elif command -v apt-get &> /dev/null; then
		PACKAGE_MANAGER="apt-get"
	elif command -v pacman &> /dev/null; then
		PACKAGE_MANAGER="pacman"
  elif command -v apk &>/dev/null; then
		PACKAGE_MANAGER="apk"
  elif command -v dnf &>/dev/null; then
    echo "WARNING: dnf package manager support is experimental"
    PACKAGE_MANAGER="dnf"
	else
		echo "Unable to find supported package manager (yum, apt-get, dnf, or pacman). Abort"
		exit 1
	fi
elif [[ "$(uname)" == "Darwin" ]]; then
	if command -v brew &>/dev/null; then
		PACKAGE_MANAGER="brew"
	else
		echo "Missing package manager Homebrew (https://brew.sh/). Abort"
		exit 1
	fi
else
	echo "Unknown OS. Abort."
	exit 1
fi

export DOTNET_INSTALL_DIR="${HOME}/.dotnet/"
if [[ "$OPT_DIR" == "true" ]]; then
  export DOTNET_INSTALL_DIR="/opt/dotnet/"
  mkdir -p "$DOTNET_INSTALL_DIR" || true
fi
install_rustup
install_z3
install_dotnet
install_boogie
update_path_and_profile
cargo install --git https://github.com/diem/diem move-cli --branch main
cargo install --git https://github.com/diem/diem shuffle --branch main