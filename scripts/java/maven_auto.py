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
UNSUPPORTED = 'unsupported-platform-set-z3.platform'


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
    element('description').text = ('Unpublished Maven-only platform selector. Set z3.platform explicitly '
                                   'when the build host differs from the deployment target.')
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
            prop = child(activation, 'property')
            child(prop, 'name', '!z3.platform')
            child(child(profile, 'properties'), 'z3.platform', platform)
    # Dependency POM properties normally take precedence over CLI properties.
    # As in OpenJFX, a self-referencing property in an explicitly activated
    # profile lets the supplied CLI value replace that POM default.
    override = child(profiles, 'profile')
    child(override, 'id', 'z3-platform-override')
    child(child(child(override, 'activation'), 'property'), 'name', 'z3.platform')
    child(child(override, 'properties'), 'z3.platform', '${z3.platform}')
    ET.indent(root, space='  ')
    return ET.tostring(root, encoding='utf-8', xml_declaration=True) + b'\n'
