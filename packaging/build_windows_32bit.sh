#!/usr/bin/env bash

set -euo pipefail

if which dpkg-query >/dev/null; then
    if dpkg-query -W g++-mingw-w64-i686 mingw-w64-i686-dev \
            build-essential libtool autotools-dev automake pkg-config \
            bsdmainutils curl ca-certificates; then
        echo "All dependencies satisfied."
    else
        echo "Missing dependencies detected. Exiting..."
        exit 1
    fi
    # sudo update-alternatives --config i686-w64-mingw32-g++ # you have to select posix
fi


if which ccache >/dev/null; then
    echo "ccache config:"
    ccache -ps
fi

export CXXFLAGS="${CXXFLAGS:--frecord-gcc-switches}"
echo "CXXFLAGS set to $CXXFLAGS"

pushd depends
make -j`getconf _NPROCESSORS_ONLN` HOST=i686-w64-mingw32 NO_QT=1 V=1
popd

./autogen.sh
DEPS_DIR=`pwd`/depends/i686-w64-mingw32
CONFIG_SITE=${DEPS_DIR}/share/config.site ./configure --prefix=/ --without-gui --with-icu="$DEPS_DIR" --enable-static --disable-shared
make -j`getconf _NPROCESSORS_ONLN`
i686-w64-mingw32-strip src/lbrycrdd.exe src/lbrycrd-cli.exe src/lbrycrd-tx.exe

if which ccache >/dev/null; then
    echo "ccache stats:"
    ccache -s
fi

echo "Windows 32bit build is complete"
