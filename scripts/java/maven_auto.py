############################################
# Copyright (c) 2026 Microsoft Corporation
# Prepare an optional POM-only selector for unpublished Maven rehearsals.
############################################
from xml.etree import ElementTree as ET

from maven_artifacts import NS, pom_text


# Match JVM architecture aliases explicitly. Generate profiles only for the
# platforms actually present in the prepared family, not every known mapping.
SYSTEMS = {'linux': ('name', 'Linux'), 'win': ('family', 'Windows'), 'osx': ('family', 'Mac')}
ARCHES = {'x64': ('amd64', 'x86_64', 'x64'), 'arm64': ('aarch64', 'arm64')}
UNSUPPORTED = 'unsupported-platform-use-explicit-classifier'


def identity(report):
    return {**report['maven'], 'artifactId': report['maven']['artifactId'] + '-auto'}


def pom(report):
    selected = identity(report)
    root = ET.fromstring(pom_text(selected, report['source_commit']))
    def child(parent, name, text=None):
        node = ET.SubElement(parent, '{' + NS + '}' + name)
        node.text = text
        return node
    def element(name):
        return root.find('{' + NS + '}' + name)
    element('packaging').text = 'pom'
    element('name').text = 'Z3 Java platform selector'
    element('description').text = ('Unpublished Maven-only host platform selector. Use an explicit runtime '
                                   'classifier when the deployment target differs from the build host.')
    properties = child(root, 'properties')
    # Unknown platforms must fail dependency resolution rather than silently
    # selecting a different architecture or the universal JAR.
    child(properties, 'z3.platform', UNSUPPORTED)
    dependencies = child(root, 'dependencies')
    dependency = child(dependencies, 'dependency')
    for key in ('groupId', 'artifactId', 'version'):
        child(dependency, key, report['maven'][key])
    child(dependency, 'classifier', '${z3.platform}')
    profiles = child(root, 'profiles')
    for platform in sorted(report['platforms']):
        system, arch = platform.split('-')
        if system not in SYSTEMS or arch not in ARCHES:
            raise ValueError('Unknown selector platform: ' + platform)
        for alias in ARCHES[arch]:
            profile = child(profiles, 'profile')
            child(profile, 'id', 'z3-' + platform + '-' + alias)
            activation = child(profile, 'activation')
            os = child(activation, 'os')
            field, value = SYSTEMS[system]
            child(os, field, value)
            child(os, 'arch', alias)
            child(child(profile, 'properties'), 'z3.platform', platform)
    ET.indent(root, space='  ')
    return ET.tostring(root, encoding='utf-8', xml_declaration=True) + b'\n'
