#!/usr/bin/env python

import subprocess
import coloredlogs
import logging
import sys
import json
import os
# import re

log_format = '%(levelname)s %(message)s'
coloredlogs.install(level='INFO', fmt=log_format)
# coloredlogs.install(level='DEBUG', fmt=log_format)
logging.basicConfig(stream=sys.stderr, level=logging.DEBUG)

def compiler_verify(features: list = []):

    def analyze_compiler_message(msg: dict):
        compiler_enforcement = \
            {'unsafe': ('vio-unsafe', 'PoBF forbids unsafe code in this souce file, please try to remove it.'),
             'but its trait bounds were not satisfied': ('vio-typestate', 'The code may try to call a function which is not available in this state.'),
             'private field': ('vio-private','The code may try to access a private filed which can contain secret information'),
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
                logging.warning('the detailed explaination of this error type [%s] can be found in the document', vio_type)

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
        match o['reason']:
            case 'compiler-message': analyze_compiler_message(o)
            case 'build-finished':
                return o["success"]


def mirai_verify():

    def analyze_mirai_message(msg: dict):
        mirai_enforcement = \
            {'warning: possible false verification condition': ('vio-ocall', 'PoBF only allows const printing in the enclave.') }
        
        details = msg['message']['rendered']
        logging.debug(details)

        error_captured = False
        for identifier, (vio_type, explaination) in mirai_enforcement.items():

            if identifier in details:
                # if re.search(identifier, details):
                error_captured = True
                logging.error(explaination)
                logging.warning('the detailed explaination of this error type [%s] can be found in the document', vio_type)

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
        match o['reason']:
            case 'compiler-message': analyze_mirai_message(o)

def src_verifier():

    def check_unsafe(path: str) -> bool:
        logging.info("- analyzing file: %s...", path)
        unsafe_allowed = ['src/lib.rs', 'src/utils.rs', 'src/bogus.rs']

        if list(filter(lambda x: x in path, unsafe_allowed)):
            logging.info("  + unsafe code not forbidden in %s, and this is allowed", path)
            return True

        with open(path, 'r') as f:
            if list(filter(lambda l: l.startswith('#![forbid(unsafe_code)]'), f.readlines())):
                logging.info("  + unsafe code fobidden in %s, clear", path)
                return True
            else:
                logging.error("  + unsafe code not forbidden in %s, please add `#![forbid(unsafe_code)]` in this file!", path)
                return False

    logging.info("checking unsafe code...")

    for root, _, files in os.walk("./src", topdown=False):
        for name in files:
            logging.debug(os.path.join(root, name))
            filename = os.path.join(root, name)
            check_unsafe(filename)


def main():
    if compiler_verify():
        logging.info(
            "Compiler verification passed. Your code will be verified towrads MIRAI.")
    else:
        logging.error(
            "Compiler verification Failed. Please remove the potentially dangerous operations.")
        return 1

    mirai_verify()

def demo():
    logging.info('PoBF demo of potential violations.')
    logging.info('Violation: unsafe code')
    compiler_verify(['vio_unsafe'])
    logging.info('Violation: private field access')
    compiler_verify(['vio_private'])
    logging.info('Violation: typestate violation')
    compiler_verify(['vio_typestate'])
    logging.info('Violation: ocall containing secret')
    compiler_verify(['vio_ocall'])

    mirai_verify()

    src_verifier()

if __name__ == "__main__":
    demo()
