'''
title           : blockchain.py
description     : A blockchain implemenation
author          : Adil Moujahid
date_created    : 20180212
date_modified   : 20180309
version         : 0.5
usage           : python blockchain.py
                  python blockchain.py -p 5000
                  python blockchain.py --port 5000
python_version  : 3.6.1
Comments        : The blockchain implementation is mostly based on [1].
                  I made a few modifications to the original code in order to add RSA encryption to the transactions
                  based on [2], changed the proof of work algorithm, and added some Flask routes to interact with the
                  blockchain from the dashboards
References      : [1] https://github.com/dvf/blockchain/blob/master/blockchain.py
                  [2] https://github.com/julienr/ipynb_playground/blob/master/bitcoin/dumbcoin/dumbcoin.ipynb
'''

# ToDO: change mining_sender to port number(self.node_id) and perhaps sender address in transaction?

from collections import OrderedDict

import binascii

import Crypto
import Crypto.Random
from Crypto.Hash import SHA
from Crypto.PublicKey import RSA
from Crypto.Signature import PKCS1_v1_5
import hashlib
import json
from time import time
from urllib.parse import urlparse
import sys
import requests
from flask import Flask, jsonify, request, render_template
from flask_cors import CORS
import random

MINING_SENDER = "THE BLOCKCHAIN"
MINING_REWARD = 1
MINING_DIFFICULTY = 4


class Wallet(object):
    """
    A wallet is a private/public key pair
    """

    def __init__(self):
        random_gen = Crypto.Random.new().read
        self._private_key = RSA.generate(1024, random_gen)
        self._public_key = self._private_key.publickey()
        self._signer = PKCS1_v1_5.new(self._private_key)

    @property
    def address(self):
        """We take a shortcut and say address is public key"""
        return binascii.hexlify(self._public_key.exportKey(format='DER')).decode('ascii')

    def sign(self, message):
        """
        Sign a message with this wallet
        """
        h = SHA.new(message.encode('utf8'))
        return binascii.hexlify(self._signer.sign(h)).decode('ascii')


class Blockchain:

    def __init__(self):

        self.transactions = []

        self.nodes = set()
        self.node_id = sys.argv[1]  # example: 539027a6798a4e248578481f2d82e758
        self.chain = []
        self.create_block(1, time(), self.node_id, 'NO_NONCE', 'GENESIS_BLOCK', 'NO_TRANSACTIONS', 0)


    def register_node(self, node_url):
        """
        Add a new node to the list of nodes
        """
        # Checking node_url has valid format
        parsed_url = urlparse(node_url)
        if parsed_url.netloc:
            self.nodes.add(parsed_url.netloc)
        elif parsed_url.path:
            # Accepts an URL without scheme like '192.168.0.5:5000'.
            self.nodes.add(parsed_url.path)
        else:
            raise ValueError('Invalid URL')

    def verify_transaction_signature(self, sender_address, signature, transaction):
        """
        Check that the provided signature corresponds to transaction
        signed by the public key (sender_address)
        """
        print(sender_address)
        public_key = RSA.importKey(binascii.unhexlify(sender_address))
        verifier = PKCS1_v1_5.new(public_key)
        h = SHA.new(str(transaction).encode('utf8'))
        return verifier.verify(h, binascii.unhexlify(signature))

    def submit_transaction(self, sender_address, recipient_address, value, signature):
        """
        Add a transaction to transactions array if the signature verified
        """
        transaction = OrderedDict({'sender_address': sender_address,
                                   'recipient_address': recipient_address,
                                   'value': value})

        # Reward for mining a block
        if sender_address == MINING_SENDER:
            self.transactions.append(transaction)
            return len(self.chain) + 1
        # Manages transactions from wallet to another wallet
        else:
            transaction_verification = self.verify_transaction_signature(sender_address, signature, transaction)
            if transaction_verification:
                self.transactions.append(transaction)
                return len(self.chain) + 1
            else:
                return False

# ToDo: sort parameters passed to this from file read chain.
    def create_block(self, block_number, timestamp, miner, nonce, previous_hash, transactions, read_mode = 0):
        """
        Add a block of transactions to the blockchain
        """
        if read_mode == 0:
            if block_number == 1:
                pass
            else:
                block_number == len(self.chain) + 1
            timestamp = time()
            miner = self.node_id
            transactions = self.transactions

        # ToDo: check these parameters work
        block = {'block_number': block_number,
                 'timestamp': timestamp,
                 'miner': miner,
                 'nonce': nonce,
                 'previous_hash': previous_hash,
                 'transactions': transactions}
        # Reset the current list of transactions
        self.transactions = []

        self.chain.append(block)
        return block

    def hash(self, block):
        """
        Create a SHA-256 hash of a block
        """
        # We must make sure that the Dictionary is Ordered, or we'll have inconsistent hashes
        block_string = json.dumps(block, sort_keys=True).encode()
        return hashlib.sha256(block_string).hexdigest()

    def proof_of_work(self):
        """
        Proof of work algorithm
        """
        last_block = self.chain[-1]
        last_hash = self.hash(last_block)
        nonce = 0
        while self.valid_proof(self.transactions, last_hash, nonce) is False:
            nonce += 1
        return nonce

    def valid_proof(self, transactions, last_hash, nonce, difficulty=MINING_DIFFICULTY):
        """
        Check if a hash value satisfies the mining conditions. This function is used within the proof_of_work function.
        """
        guess = (str(transactions) + str(last_hash) + str(nonce)).encode()
        guess_hash = hashlib.sha256(guess).hexdigest()
        return guess_hash[:difficulty] == '0' * difficulty

    def valid_chain(self, chain):
        """
        check if a blockchain is valid
        """
        last_block = chain[0]
        current_index = 1

        while current_index < len(chain):
            block = chain[current_index]

            if block['previous_hash'] != self.hash(last_block):
                return False

            # Check that the Proof of Work is correct
            # Delete the reward transaction
            transactions = block['transactions'][:-1]
            # Need to make sure that the dictionary is ordered. Otherwise we'll get a different hash
            transaction_elements = ['sender_address', 'recipient_address', 'value']
            transactions = [OrderedDict((k, transaction[k]) for k in transaction_elements) for transaction in
                            transactions]

            if not self.valid_proof(transactions, block['previous_hash'], block['nonce'], MINING_DIFFICULTY):
                return False

            last_block = block
            current_index += 1

        return True

    def resolve_conflicts(self):
        """
        Resolve conflicts between blockchain's nodes
        by replacing our chain with the longest one in the network.
        """
        neighbours = self.nodes
        new_chain = None

        # We're only looking for chains longer than ours
        max_length = len(self.chain)

        # Grab and verify the chains from all the nodes in our network
        for node in neighbours:
            print('http://' + node + '/chain')
            response = requests.get('http://' + node + '/chain')

            if response.status_code == 200:
                length = response.json()['length']
                chain = response.json()['chain']

                # Check if the length is longer and the chain is valid
                if length > max_length and self.valid_chain(chain):
                    max_length = length
                    new_chain = chain

        # Replace our chain if we discovered a new, valid chain longer than ours
        if new_chain:
            self.chain = new_chain
            return True

        return False

    def populate_transactions(self):
        """ensure that transactions are always ready to be put in blocks"""
        while len(blockchain.transactions) <= 20:
            address1 = wallets[random.randint(0, 9)]
            address2 = wallets[random.randint(0, 9)]
            while address2 == address1:
                address2 = wallets[random.randint(0, 9)]
            value = random.randint(0, 5)

            transaction = OrderedDict({'sender_address': address1.address,
                                       'recipient_address': address2.address,
                                       'value': value})
            self.transactions.append(transaction)

        print("Twenty transactions added to Transaction pool..")

    def populate_sec_transactions(self):
        # TODO: look into parameters passed to self.verify_transaction_signature
        """ensure that transactions are always ready to be put in blocks"""
        while len(blockchain.transactions) <= 20:
            address1 = wallets[random.randint(0, 9)]
            address2 = wallets[random.randint(0, 9)]
            while address2 == address1:
                address2 = wallets[random.randint(0, 9)]
            value = random.randint(0, 5)

            transaction = OrderedDict({'sender_address': address1.address,
                                       'recipient_address': address2.address,
                                       'value': value})
            transaction_verification = self.verify_transaction_signature(address1.address, address1.sign(transaction),
                                                                         transaction)
            if transaction_verification:
                self.transactions.append(transaction)
                print("Transaction %d added" % len(blockchain.transactions))
            else:
                print("Transaction %d failed" % len(blockchain.transactions))

        print("Twenty transactions added to Transaction pool..")



    def internal_mine(self):
        # We run the proof of work algorithm to get the next proof...
        # check file chain length against self chain length.
        blockchain.populate_transactions()
        print("\nMining..")
        nonce = self.proof_of_work()

        with open('chain.txt') as file:
            chainlength = int(file.readline())
            print('Blocklength of text file:%s' % chainlength)
        # ToDo: changed 'len(self.chain) < chainlength:' to 'len(self.chain)-1 < chainlength:'
        if len(self.chain)-1 < chainlength:
            if len(self.chain) == 1:
                self.chain = []
            self.get_chain()

        if len(self.chain) == chainlength:
            # ToDo: check timestamp on last block for latest version
            pass

        if len(self.chain) > chainlength:
            writedata = [str(len(self.chain)), '\n']

            for block in self.chain:
                for transac in block.items():
                    tuples = ''.join(str(transac))
                    writedata.append(tuples)
                writedata.append('\n')

            with open('chain.txt','w') as file:
                file.writelines(writedata)
                print("File updated to %d blocks.." % (len(self.chain)))
                # for block in self.chain:
                #    file.writelines(block)


        last_block = self.chain[-1]


        # We must receive a reward for finding the proof.
        self.submit_transaction(sender_address=MINING_SENDER,
                                recipient_address=blockchain.node_id,
                                value=MINING_REWARD, signature="")

        # Forge the new Block by adding it to the chain
        previous_hash = self.hash(last_block)
        block = self.create_block(len(self.chain) + 1, time(), self.node_id, nonce, previous_hash, self.transactions, 0)

        print("New Block Forged:- block number: %d, no.transactions: %d, nonce: %d, previous_hash %s"
              % (block['block_number']-1, len(block['transactions'])-1, block['nonce'], block['previous_hash']))

        return True

    def get_chain(self):
        file_chain = []
        transactions = []
        block_number = 0
        timestamp = 0
        miner = 0
        nonce = 0
        previous_hash = 0
        sender_address = 0
        recipient_address = 0
        value = 0

        with open('chain.txt') as file:
            for line in file:
                # print(line)
                for half in line.split('transactions'):
                    for token in half.split(')'):
                        if token == '\n':
                            self.create_block(block_number, timestamp, miner, nonce, previous_hash, transactions, 1)
                            transactions = []
                        token = token.replace('(', '')
                        token = token.replace('[', '')
                        token = token.replace(']', '')
                        token = token.replace('\'', '')
                        token = token.replace('transactions', '')
                        token = token.lstrip(',')
                        token = token.strip()
                        token = token.replace('OrderedDict', '')
                        # print('token = %s' % token)
                        if token.rpartition(',')[0] == 'block_number':
                            block_number = str(token.replace(' ', '').rpartition(',')[2])
                        # print('***block number = %s' % block_number)
                        if token.rpartition(',')[0] == 'timestamp':
                            timestamp = str(token.replace(' ', '').rpartition(',')[2])
                        # print('***timestamp = %s' % timestamp)
                        if token.rpartition(',')[0] == 'miner':
                            miner = str(token.replace(' ', '').rpartition(',')[2])
                        # print('***miner = %s' % miner)
                        if token.rpartition(',')[0] == 'nonce':
                            nonce = str(token.replace(' ', '').rpartition(',')[2])
                        # print('***nonce = %s' % nonce)
                        if token.rpartition(',')[0] == 'previous_hash':
                            previous_hash = str(token.replace(' ', '').rpartition(',')[2])
                        # print('***previous_hash = %s' % previous_hash)
                        if token.rpartition(',')[0] == 'sender_address':
                            sender_address = str(token.rpartition(',')[2].strip())
                        if token.rpartition(',')[0] == 'recipient_address':
                            recipient_address = str(token.rpartition(',')[2].strip())
                        if token.rpartition(',')[0] == 'value':
                            value = str(token.rpartition(',')[2].strip())
                            transaction = OrderedDict({'sender_address': sender_address,
                                                        'recipient_address': recipient_address,
                                                        'value': value})
                            transactions.append(transaction)
                            # print('***transaction appended to array = %s' % transaction)

def create_wallets():
    # Instantiate Wallets x10
    temp_wallets = (Wallet(),
                    Wallet(),
                    Wallet(),
                    Wallet(),
                    Wallet(),
                    Wallet(),
                    Wallet(),
                    Wallet(),
                    Wallet(),
                    Wallet())
    return temp_wallets


# Instantiate the Flask Node
app = Flask(__name__)
CORS(app)

# Instantiate the Blockchain
blockchain = Blockchain()
wallets = create_wallets()
print('self.node_id = %s' % blockchain.node_id)

while 1:

    blockchain.internal_mine()



@app.route('/')
def index():
    return render_template('./index.html')


@app.route('/configure')
def configure():
    return render_template('./configure.html')


@app.route('/transactions/new', methods=['POST'])
def new_transaction():
    values = request.form

    # Check that the required fields are in the POST'ed data
    required = ['sender_address', 'recipient_address', 'amount', 'signature']
    if not all(k in values for k in required):
        return 'Missing values', 400
    # Create a new Transaction
    transaction_result = blockchain.submit_transaction(values['sender_address'], values['recipient_address'],
                                                       values['amount'], values['signature'])

    if transaction_result == False:
        response = {'message': 'Invalid Transaction!'}
        return jsonify(response), 406
    else:
        response = {'message': 'Transaction will be added to Block ' + str(transaction_result)}
        return jsonify(response), 201


@app.route('/transactions/get', methods=['GET'])
def get_transactions():
    # Get transactions from transactions pool
    transactions = blockchain.transactions

    response = {'transactions': transactions}
    return jsonify(response), 200


@app.route('/chain', methods=['GET'])
def full_chain():
    response = {
        'chain': blockchain.chain,
        'length': len(blockchain.chain),
    }
    return jsonify(response), 200

@app.route('/mine', methods=['GET'])
def mine():
    # We run the proof of work algorithm to get the next proof...
    last_block = blockchain.chain[-1]
    nonce = blockchain.proof_of_work()

    # We must receive a reward for finding the proof.
    blockchain.submit_transaction(sender_address=MINING_SENDER, recipient_address=blockchain.node_id,
                                  value=MINING_REWARD, signature="")

    # Forge the new Block by adding it to the chain
    previous_hash = blockchain.hash(last_block)
    block = blockchain.create_block(nonce, previous_hash)

    response = {
        'message': "New Block Forged",
        'block_number': block['block_number'],
        'transactions': block['transactions'],
        'nonce': block['nonce'],
        'previous_hash': block['previous_hash'],
    }
    return jsonify(response), 200


@app.route('/nodes/register', methods=['POST'])
def register_nodes():
    values = request.form
    nodes = values.get('nodes').replace(" ", "").split(',')

    if nodes is None:
        return "Error: Please supply a valid list of nodes", 400

    for node in nodes:
        blockchain.register_node(node)

    response = {
        'message': 'New nodes have been added',
        'total_nodes': [node for node in blockchain.nodes],
    }
    return jsonify(response), 201


@app.route('/nodes/resolve', methods=['GET'])
def consensus():
    replaced = blockchain.resolve_conflicts()

    if replaced:
        response = {
            'message': 'Our chain was replaced',
            'new_chain': blockchain.chain
        }
    else:
        response = {
            'message': 'Our chain is authoritative',
            'chain': blockchain.chain
        }
    return jsonify(response), 200


@app.route('/nodes/get', methods=['GET'])
def get_nodes():
    nodes = list(blockchain.nodes)
    response = {'nodes': nodes}
    return jsonify(response), 200


# if __name__ == '__main__':
from argparse import ArgumentParser
parser = ArgumentParser()
parser.add_argument('-p', '--port', default=5000, type=int, help='port to listen on')
args = parser.parse_args()
port = args.port

app.run(host='127.0.0.1', port=port)
