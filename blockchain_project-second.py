'''
title           : blockchain_project.py
description     : Blockchain implementation
author          : Ben Gladders
date_created    : 01012020
date_modified   : 22/04/2020
version         : 0.9
usage           : python blockchain.py [number_of_workers]

python_version  : 3.6
Comments        : This Blockchain was based on Adil Moujahid's Blockchain @ [1], with some modifications to how the
                    System runs. [1] generates an RSA wallet string in hex, but requires the user to remember this
                    digest; for each client.
                    Every time a miner is required to mine, the user has to manually enter transaction detail
                    and press mine. This made multiple nodes almost impossible to mine at once. The
                    Web front end is not utilised, as searching for nodes is not possible, and adding by intended port
                    number doesnt seem to find anything.
                    Used a coordinator to start multiple nodes mining-at-once automatically, on "multiprocessing"
                    library function.
                    This allows python to use multiple processors, but requires opening message queueing system, as
                    memory space cant be safely shared between processes. This required Pickleable objects to be passed
                    through the message queue duplex-pipeline.
                    All nodes take turns to acquire Global Interpreter Lock and read from Blockchain file, then wait for
                    "go" in the event flag and when one successfully finds the node, messages back to coordinator;
                    writing to the chain. The event flag is set to low signalling all nodes to stop and restart.
                    Each node checks every 10 nonce's for other nodes success.
References      : [1] https://github.com/adilmoujahid/blockchain-python-tutorial/blob/master/blockchain/blockchain.py
'''



from collections import OrderedDict

import binascii
import multiprocessing
import Crypto
import Crypto.Random
from Crypto.Hash import SHA
from Crypto.PublicKey import RSA
from Crypto.Signature import PKCS1_v1_5

import hashlib
import json
from time import time
from uuid import uuid4
import sys
from time import sleep

import requests
import random

MINING_SENDER = "THE BLOCKCHAIN"
MINING_REWARD = 1
MINING_DIFFICULTY = 5
filename = 'chain.txt'
transactions = []


class Wallet(object):
    """
    A wallet is an RSA private/public key pair, purely fictitious for generating transactions between users.
    """

    def __init__(self):
        random_gen = Crypto.Random.new().read
        self._private_key = RSA.generate(1024, random_gen)  # Generate new public/private key pair using RSA
        self._public_key = self._private_key.publickey()  # split public key from private
        self._signer = PKCS1_v1_5.new(self._private_key)  #

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
    """
    Blockchain object for each node on network
    """
    def __init__(self, incoming_task, outgoing_task, proc_event, passed_trans, passed_chainlength, proc_lock):

        self.nodes = set()
        # Generate random number to be used as node_id
        self.node_id = str(uuid4()).replace('-', '')  # example: 539027a6798a4e248578481f2d82e758
        self.chain = []
        self.incoming_task = incoming_task  # multiprocess messaging queue in
        self.outgoing_task = outgoing_task  # multiprocess messaging queue out
        self.proc_event = proc_event
        self.transactions = passed_trans
        self.chain_length = passed_chainlength
        self.proc_lock = proc_lock
        self.send_id()  # register self on node list @ coordinator
        self.internal_mine()  # start self mining


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
    def create_block(self, block_number, timestamp, miner, nonce, previous_hash, trans, read_mode=0):
        """
        Add a block of transactions to the blockchain
        """
        if read_mode == 0:
            if block_number == 1:
                pass
            else:
                block_number = len(self.chain) + 1
                miner = self.node_id
                trans = self.transactions

        block = {'block_number': block_number,
                 'timestamp': timestamp,
                 'miner': miner,
                 'nonce': nonce,
                 'previous_hash': previous_hash,
                 'transactions': trans}

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
        if len(self.chain)<1:
            last_block = self.create_block(1,
                                           time(),
                                           'BLOCKCHAIN',
                                           'NO_NONCE',
                                           'GENESIS_BLOCK',
                                           'NO_TRANSACTIONS',
                                           0)
        else:
            last_block = self.chain[-1]
        last_hash = self.hash(last_block)
        chainlength_same = True
        nonce = 0
        while self.valid_proof(self.transactions, last_hash, nonce) is False:
            nonce += 1
            if not self.proc_event.is_set():
                return -1
        return nonce


    def valid_proof(self, trans, last_hash, nonce, difficulty=MINING_DIFFICULTY):
        """
        Check if a hash value satisfies the mining conditions. This function is used within the proof_of_work function.
        """
        guess = (str(trans) + str(last_hash) + str(nonce)).encode()
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
            # Check that the hash of the block is correct
            if block['previous_hash'] != self.hash(last_block):
                return False

            # Check that the Proof of Work is correct
            # Delete the reward transaction
            trans = block['transactions'][:-1]
            # Need to make sure that the dictionary is ordered. Otherwise we'll get a different hash
            transaction_elements = ['sender_address', 'recipient_address', 'value']
            trans = [OrderedDict((k, transaction[k]) for k in transaction_elements) for transaction in trans]

            if not self.valid_proof(trans, block['previous_hash'], block['nonce'], MINING_DIFFICULTY):
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

    def populate_sec_transactions(self):
        """ensure that transactions are always ready to be put in blocks"""
        while len(transactions) <= 20:
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
                print("Transaction %d added" % len(transactions))
            else:
                print("Transaction %d failed" % len(transactions))

        print("Twenty transactions added to Transaction pool..")

# ToDo: THIS IS WHERE GOT TO.
    def internal_mine(self):
        while True:
            # We run the proof of work algorithm to get the next proof...
            self.get_chain()
            self.signal_ready()
            sleep(1)
            self.proc_event.wait()
            self.get_transactions()

            nonce = self.proof_of_work()

            if not nonce == -1:  # if mining nonce is success
                self.proc_lock.acquire()
                self.create_reward()
                if len(self.chain) < 1:
                    self.create_block(1,
                                      time(),
                                      'BLOCKCHAIN',
                                      'NO_NONCE',
                                      'GENESIS_BLOCK',
                                      'NO_TRANSACTIONS',
                                      0)

                last_block = self.chain[-1]
                last_hash = self.hash(last_block)
                self.create_block(len(self.chain) + 1, time(), self.node_id, nonce, last_hash, self.transactions)
                self.write_chain()
                self.outgoing_task.put([self.node_id, 'finished'])
                print("Node:%s File updated to %d blocks.." % (self.node_id, len(self.chain)))
                self.proc_lock.release()
                sleep(1)

            else:  # if beaten to the nonce by other node
                self.proc_lock.acquire()
                self.outgoing_task.put([self.node_id, 'finished'])
                print('Node:%s Finished mining as beaten.' % self.node_id)
                self.proc_lock.release()
            sleep(1)  # must wait to allow coordinator to register nodes finished
            self.proc_event.wait()

    def get_chain(self):
        self.chain = []
        trans = []
        # initialise values incase of if/else not finding values before use..
        block_number = 0
        timestamp = 0
        miner = 0
        nonce = 0
        previous_hash = 0
        sender_address = 0
        recipient_address = 0
        value = 0

        self.proc_lock.acquire()
        print('Node:%s Acquiring latest chain..' % self.node_id)
        with open(filename) as file:
            for line in file:
                # print(line)
                for half in line.split('transactions'):
                    for token in half.split(')'):
                        if token == '\n':
                            # if len(file_chain) == 0:
                            #    transactions.append(OrderedDict({'sender_address': 'GENESIS',
                             #                                    'recipient_address': 'GENESIS',
                             #                                    'value': 'GENESIS'}))
                            self.create_block(int(block_number), timestamp, miner, nonce, previous_hash, trans, 1)
                            trans = []
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
                            curr_trans = OrderedDict({'sender_address': sender_address,
                                                        'recipient_address': recipient_address,
                                                        'value': value})
                            trans.append(curr_trans)
                            # print('***transaction appended to array = %s' % transaction)
        print('Node:%s chain acquired.. waiting' % self.node_id)
        self.proc_lock.release()

    def write_chain(self):
        writedata = [str(len(self.chain)), '\n']  # length of chain at top of file

        for block in self.chain:
            for transac in block.items():
                tuples = ''.join(str(transac))
                writedata.append(tuples)
            writedata.append('\n')

        try:
            with open(filename, 'w') as file:
                file.writelines(writedata)
                print("File updated to %d blocks.." % (len(self.chain)))
        except IOError:
            print('Could not read file %s' % str(filename))

    def create_reward(self):
        # We must receive a reward for finding the proof.
        self.submit_transaction(sender_address=MINING_SENDER,
                                recipient_address=self.node_id,
                                value=MINING_REWARD, signature="")

    def send_id(self):
        sleep(0.5)
        self.proc_lock.acquire()
        print('Node:%s sending id to parent..' % self.node_id)
        self.outgoing_task.put([self.node_id, 'id'])
        self.proc_lock.release()
        self.proc_event.wait()

    def signal_ready(self):
        self.proc_lock.acquire()
        self.outgoing_task.put([self.node_id, 'ready'])
        self.proc_lock.release()

    def get_transactions(self):
        self.proc_lock.acquire()
        print('Node:%s getting transactions from parent.' % self.node_id)
        self.transactions = self.incoming_task.get(block=True)
        print('Node:%s got transactions.\n' % self.node_id)
        self.proc_lock.release()


def populate_transactions(walls):
    """ensure that transactions are always ready to be put in blocks"""
    trans = []
    while len(trans) < 20:
        address1 = walls[random.randint(0, 9)]
        address2 = walls[random.randint(0, 9)]
        while address2 == address1:
            address2 = walls[random.randint(0, 9)]
        value = random.randint(0, 5)

        transaction = OrderedDict({'sender_address': address1.address,
                                   'recipient_address': address2.address,
                                   'value': value})
        trans.append(transaction)
    print("Coordinator: Twenty transactions added to Transaction pool..")
    return trans


def create_wallets():
    # Instantiate Wallets x10
    # ToDo: create for loop here. (temp_wallets.append(wallet() for i in range(10)))

    temp_wallets = [Wallet() for i in range(10)]

    print('Wallets created == %d' % len(temp_wallets))
    return temp_wallets


def get_chainlength(file_name):
    chainlength = 0
    retries = 0
    print('DEBUG..start of get_chainlength')
    lock.acquire()
    while chainlength < 1 and retries < 3:
        try:
            with open(file_name, 'a+') as file:
                try:
                    file.seek(0)
                    chainlength = int(file.readline())
                except ValueError:
                    write_data = ['1\n(\'block_number\', 1)'
                                  '(\'timestamp\', 1583940322.698881)'
                                  '(\'miner\', \'BLOCKCHAIN\')'
                                  '(\'nonce\', \'NO_NONCE\')'
                                  '(\'previous_hash\', \'GENESIS_BLOCK\')'
                                  '(\'transactions\', [])\n']
                    file.writelines(write_data)
                    retries += 1
                    # chainlength = int(file.readline())
                print('Blocklength of text file:%s' % chainlength)
        except IOError:
            print('Could not read file %s' % str(file_name))
            chainlength = -1
            retries += 1
    if chainlength < 1:
        print('Chainlength is invalid, so file not likely available. Quitting to OS.')
        sys.exit()
    lock.release()
    print("DEBUG..lock released in chainlength")
    return chainlength

def print_queue_size(queue, queue_name):
    print('DEBUG.. %s size = %d' % (queue_name, queue.qsize()))

if __name__ == '__main__':
    # ToDo: Try: Except: Check number of processes doesnt exceed Hyperthreads in cpu.
    args = sys.argv
    print('Requested %s qty_processes' % args[1])
    if int(args[1]) > multiprocessing.cpu_count():
        print('**COMMAND-LINE PARAMETER[1] IS GREATER THAN CPU CORES..EXITING**')
        sys.exit()
    else:
        qty_processes = int(args[1])

    outgoing_msg = multiprocessing.Queue()  # create multiprocessing queue to control program flow through messaging
    incoming_msg = multiprocessing.Queue()
    e = multiprocessing.Event()  # event trigger to synchronise processes
    process_array = []
    lock = multiprocessing.Lock()  # passed ticket system to control one-at-a-time access to Python GIL.

    wallets = create_wallets()
    transactions = []
    file_chainlength = get_chainlength(filename)

    nodes = {}


    for i in range(qty_processes):

        p = multiprocessing.Process(target=Blockchain, args=(outgoing_msg, incoming_msg, e, transactions, file_chainlength, lock))
        process_array.append(p)
        p.start()

    while len(nodes) < qty_processes:
        node_id, status = incoming_msg.get(block=True)
        nodes[node_id] = status
    print('%d Nodes registered.' % len(nodes))
    sleep(3)

    while 1:
        #ToDO: implement command line arguments for both number of miners and pool ratio.
        print("\nBlockchain simulation starting - %d miners\n" % len(nodes))
        first_response = 1

        if not e.is_set():
            e.set()
        print('DEBUG.. ')
        sleep(2)

        while not all(value == 'ready' for value in nodes.values()):
            for i in range(len(nodes)):
                print()
                transactions = populate_transactions(wallets)
                outgoing_msg.put(transactions)
            for i in range(len(nodes)):
                node, status = incoming_msg.get(block=True)
                nodes[node] = status

        print('\nAll nodes ready.\n')
        sleep(2)

        while incoming_msg.empty():
            if not e.is_set():
                e.set()
            print('Parent awaiting notification of winning results..')
            sleep(0.5)
        e.clear()
        sleep(2)
        while not all(value == 'finished' for value in nodes.values()):

            print_queue_size(incoming_msg, 'incoming_msg')
            node, status = incoming_msg.get()
            if first_response == 1:
                winner = node
                first_response = 0
            nodes[node] = status
            print('Node:%s status:%s' % (node, status))

        print('Winner is %s..' % winner)
        while not incoming_msg.empty():
            print_queue_size(incoming_msg, 'incoming_msg')
            empty_queue = incoming_msg.get()
        while not outgoing_msg.empty():
            print_queue_size(outgoing_msg, 'outgoing_msg')
            empty_queue = outgoing_msg.get()
        e.set()
        sleep(1)

