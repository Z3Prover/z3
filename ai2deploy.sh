#!/usr/bin/env bash

# Deploys z3.jar and z3-natives to bintray, https://bintray.com/allenai/third_party/z3
# Requires ~/.m2/setings.xml to configure credentials for "bintray". 
# The password is the bintray access key, which can be retrieved from 
# https://bintray.com/profile/edit, the AccessKey/Show entry.
#
# Assumes the binaries are prebuilt, with the structure:
# z3-$VERSION/
# ├── com.microsoft.z3.jar
# ├── libz3.dylib
# ├── libz3.so
# ├── libz3java.dylib
# ├── libz3java.so
#
# Accesible in SBT as: 
# libraryDependencies ++= Seq(
#   "org.allenai.third_party" % "z3" % "4.4.1",
#   "org.allenai.third_party" % "z3-native" % "4.4.1"
# 
# Requires: 
# resolvers ++= Seq(Resolver.bintrayRepo("allenai", "third_party"))

# See all the commands.
set -x

# Configuration.
GROUP_ID="org.allenai.third_party"
ARTIFACT_ID="z3"
NATIVE_ARTIFACT_ID="z3-native"
VERSION="4.4.1"
REPOSITORY_ID="bintray"
# Gotcha1: use "maven" instead of "content" for the first path fragment.
# Gothca2: use ;publish=1 for the last path fragment to autopublish.
URL="https://api.bintray.com/maven/allenai/third_party/z3/;publish=1"
DLURL="https://dl.bintray.com/allenai/third_party"
DIR="./z3-$VERSION"
FILE="$DIR/com.microsoft.z3.jar"
NATIVE_FILE="$DIR/z3-native.jar"

DLLS=("libz3.dylib" "libz3.so" "libz3java.dylib" "libz3java.so")
mkdir "$DIR/native"
cp "${DLLS[@]/#/./$DIR/}" "$DIR/native/"
(cd $DIR; jar cf "./z3-native.jar" "${DLLS[@]/#/./native/}")

# Check if we've already published this version.
COMPLETE_URL="$DLURL/${GROUP_ID//.//}/$ARTIFACT_ID/$VERSION/"
if [[ `wget -S --spider "$COMPLETE_URL"  2>&1 | grep 'HTTP/1.1 200 OK'` ]]; then
  echo "$COMPLETE_URL exists. Please bump VERSION=$VERSION"
  exit 1
fi

# Deploy.
mvn deploy:deploy-file \
  -DgroupId="$GROUP_ID" \
  -DartifactId="$ARTIFACT_ID" \
  -Dversion="$VERSION" \
  -DgeneratePom=true \
  -Dpackaging=jar \
  -DrepositoryId="$REPOSITORY_ID" \
  -Durl="$URL" \
  -Dfile="$FILE"

mvn deploy:deploy-file \
  -DgroupId="$GROUP_ID" \
  -DartifactId="$NATIVE_ARTIFACT_ID" \
  -Dversion="$VERSION" \
  -DgeneratePom=true \
  -Dpackaging=jar \
  -DrepositoryId="$REPOSITORY_ID" \
  -Durl="$URL" \
  -Dfile="$NATIVE_FILE"

