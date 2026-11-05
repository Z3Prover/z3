############################################
# Copyright (c) 2026 Microsoft Corporation
# Translate internal platform keys to published Maven classifiers.
############################################

# Internal keys are .NET runtime identifiers, shared with the NuGet packaging
# path (see mk_nuget_task.py) and used unchanged for the in-JAR resource
# directories and the native cache identity. Published classifiers follow the
# os-maven-plugin spelling instead, so that ${os.detected.classifier} matches
# an artifact this project actually ships.
CLASSIFIERS = {
    'linux-x64': 'linux-x86_64',
    'linux-arm64': 'linux-aarch_64',
    'win-x64': 'windows-x86_64',
    'osx-arm64': 'osx-aarch_64',
}

REVERSE = {value: key for key, value in CLASSIFIERS.items()}


def classifier(platform):
    try:
        return CLASSIFIERS[platform]
    except KeyError:
        raise ValueError('Unknown platform key: ' + platform) from None


def platform(name):
    try:
        return REVERSE[name]
    except KeyError:
        raise ValueError('Unknown Maven classifier: ' + name) from None


def known():
    return set(CLASSIFIERS.values())
