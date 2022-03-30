#!/usr/bin/env python

from secrets import choice
import subprocess
import coloredlogs
import logging
import sys
import json
import os
import argparse

def compiler_verify(features: list = []):

    def analyze_compiler_message(msg: dict):
        compiler_enforcement = \
            {'unsafe': ('vio-unsafe', 'PoBF forbids unsafe code in this souce file, please try to remove it.'),
             'but its trait bounds were not satisfied': ('vio-typestate', 'The code may try to call a function which is not available in this state.'),
             'private field': ('vio-private', 'The code may try to access a private filed which can contain secret information'),
             'items from traits can only be used': ('vio-private', 'The code may try to access a private trait which deals with secret.'), }
        # check what causes the failure
        details = msg['message']['rendered']
        logging.debug(details)

        error_captured = False
        for identifier, (vio_type, explaination) in compiler_enforcement.items():

            if identifier in details:
                # if re.search(identifier, details):
                error_captured = True
                logging.error(explaination)
                logging.warning(
                    'the detailed explaination of this error type [%s] can be found in the document', vio_type)

        if 'aborting due to' in details:
            return

        # if details[:6] == 'error:':
        #     logging.warning('Non-PoBF related compilation error.')
        #     error_captured = True

        if error_captured:
            print(msg['message']['rendered'])

    logging.info('Compiler verification started.')
    # analyze the rust compiler output

    rustc_verify_command = "cargo build --message-format=json".split()
    for f in features:
        rustc_verify_command.append('--features')
        rustc_verify_command.append(f)

    rustc_output = subprocess.run(
        rustc_verify_command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    compiler_outputs = rustc_output.stdout.decode("utf-8").split('\n')
    compiler_outputs_serialized = []

    for i in range(len(compiler_outputs) - 1):
        # logging.debug(compiler_output[i])
        compiler_outputs_serialized.append(json.loads(compiler_outputs[i]))

    logging.debug(len(compiler_outputs))

    for o in compiler_outputs_serialized:
        if o['reason'] == 'compiler-message':
            analyze_compiler_message(o)
        if o['reason'] == 'build-finished':
            return o["success"]


def mirai_verify():

    def analyze_mirai_message(msg: dict):
        mirai_enforcement = \
            {'warning: possible false verification condition': (
                'vio-ocall', 'PoBF only allows const printing in the enclave.')}

        details = msg['message']['rendered']
        logging.debug(details)

        error_captured = False
        for identifier, (vio_type, explaination) in mirai_enforcement.items():

            if identifier in details:
                # if re.search(identifier, details):
                error_captured = True
                logging.error(explaination)
                logging.warning(
                    'the detailed explaination of this error type [%s] can be found in the document', vio_type)

        if error_captured:
            print(msg['message']['rendered'])

    # analyze the MIRAI output
    mirai_verify_command = "cargo mirai --message-format=json".split()
    mirai_output = subprocess.run(
        mirai_verify_command, stdout=subprocess.PIPE, stderr=subprocess.DEVNULL)
    mirai_output = mirai_output.stdout.decode("utf-8").split('\n')

    mirai_outputs_serialized = []
    for i in range(len(mirai_output) - 1):
        mirai_outputs_serialized.append(json.loads(mirai_output[i]))

    for o in mirai_outputs_serialized:
        if o['reason'] == 'compiler-message':
            analyze_mirai_message(o)


def src_verify(unsafe_allowed: list = []):

    def check_unsafe(path: str) -> bool:
        logging.info("- analyzing file: %s...", path)

        if list(filter(lambda x: x in path, unsafe_allowed)):
            logging.warning(
                "  + unsafe code not forbidden in %s, and this is allowed", path)
            return True

        with open(path, 'r') as f:
            if list(filter(lambda l: l.startswith('#![forbid(unsafe_code)]'), f.readlines())):
                logging.info("  + unsafe code fobidden in %s, clear", path)
                return True
            else:
                logging.error(
                    "  + unsafe code not forbidden in %s, please add `#![forbid(unsafe_code)]` in this file!", path)
                return False

    logging.info("checking unsafe code...")

    for root, _, files in os.walk("./src", topdown=False):
        for name in files:
            logging.debug(os.path.join(root, name))
            filename = os.path.join(root, name)
            check_unsafe(filename)


def clean():
    clean_command = "cargo clean".split()
    subprocess.run(clean_command, stdout=subprocess.DEVNULL, stderr=subprocess.DEVNULL)

def main():

    # option: src_verifier / mirai_verifier / compiler_verifier
    verification_matrix = {'no_leakage':  (True, True,  False),
                           'no_residue': (True, False, True),
                           'all':        (True, True,  True)}

    parser = argparse.ArgumentParser(description='PoBF Verfier')
    parser.add_argument('--property',
                        choices=verification_matrix.keys(),
                        default='all',
                        help='the property to be verified')

    parser.add_argument('--allowed-unsafe',
                        nargs='*',
                        default=[],
                        help='source code filename(s) which are allowed to contain unsafe code')

    parser.add_argument('--log-level',
                        choices=['DEBUG', 'INFO', 'WARNING', 'ERROR'],
                        default='INFO',
                        help='the log level')

    parser.add_argument('features',
                        nargs=argparse.REMAINDER,
                        help='features for cargo build')

    # TODO: feature passing

    args = parser.parse_args()

    log_format = '%(levelname)s %(message)s'
    coloredlogs.install(level=args.log_level, fmt=log_format)
    logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)

    (src_v, mirai_v, compiler_v) = verification_matrix[args.property]

    if len(args.features) > 1 and args.features[0] == '--':
        features = args.features[1:]
    else :
        features = []

    rv = 0
    if src_v:
        logging.info("checking if the source code forbids `unsafe` ...\n")
        src_verify(args.allowed_unsafe)

    if mirai_v:
        clean()
        logging.info(
            "\ninvoking MIRAI to check possible leakage through OCALLs...\n")
        if mirai_verify():
            logging.info(
                "`no_leakage` verification passed: no leakage found by MIRAI\n")
        else:
            logging.error(
                "`no_leakage` verification failed: leakage(s) found by MIRAI\n")
            rv = 1

    if compiler_v:
        clean()
        logging.info(
            "\ninvoking rust compiler to check possible secret residue...\n")
        if compiler_verify(features):
            logging.info(
                "`no_residue` verification passed: no secret residue found by rustc\n")
        else:
            logging.error(
                "`no_residue` verification failed: secret(s) residue found by rustc")
            rv = 1

    return rv

if __name__ == "__main__":
    main()
