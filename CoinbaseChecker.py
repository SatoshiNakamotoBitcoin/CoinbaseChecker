#!/usr/bin/env python3
"""
Stratum Mining.notify Parser
"""

import json
import sys
import hashlib
from datetime import datetime
from typing import Dict, Any, Optional, List


def reverse_hex(hex_string: str) -> str:
    """
    Reverse byte order of a hex string (little-endian to big-endian).
    Bitcoin hashes in Stratum are sent as 8 little-endian uint32 words.
    We reverse the word order but keep bytes within each word in the same order.
    """
    # Remove any whitespace and ensure even length
    hex_string = hex_string.strip()
    if len(hex_string) % 2 != 0:
        hex_string = '0' + hex_string
    
    # Split into 4-byte (8 hex char) words and reverse their order
    words = [hex_string[i:i+8] for i in range(0, len(hex_string), 8)]
    return ''.join(reversed(words))


def extract_height_from_coinbase(coinbase_part1: str) -> Optional[int]:
    """
    Extract block height from coinbase script per BIP 34.
    
    The coinbase_part1 in Stratum contains the beginning of a coinbase transaction:
    - 4 bytes: version
    - varint: number of inputs (always 1 for coinbase)
    - 32 bytes: previous txid (all zeros for coinbase)
    - 4 bytes: previous output index (all 0xff for coinbase)
    - varint: scriptSig length
    - scriptSig content (this is where BIP34 height is)
    
    BIP 34 specifies that the block height must be the first item
    pushed to the stack in the coinbase scriptSig.
    
    Bitcoin script push opcodes:
    - 0x01-0x4b: Push next N bytes (N = opcode value)
    - 0x4c (OP_PUSHDATA1): Next byte is length, then data
    - 0x4d (OP_PUSHDATA2): Next 2 bytes are length (LE), then data
    - 0x4e (OP_PUSHDATA4): Next 4 bytes are length (LE), then data
    """
    try:
        coinbase_hex = coinbase_part1.strip()
        
        # Need at least version + input count + prev txid + prev idx + scriptsig length
        if len(coinbase_hex) < 2 * (4 + 1 + 32 + 4 + 1):
            return None
        
        # Skip to scriptSig: 4 bytes version + 1 byte input count + 32 bytes prev txid + 4 bytes prev idx
        offset = 2 * (4 + 1 + 32 + 4)  # multiply by 2 for hex characters
        
        # Read scriptSig length (varint - we'll assume it's < 253 for simplicity)
        scriptsig_length = int(coinbase_hex[offset:offset+2], 16)
        offset += 2
        
        # Now we're at the scriptSig content
        if len(coinbase_hex) < offset + 2:
            return None
            
        scriptsig = coinbase_hex[offset:]
        
        # Read the first byte (opcode) of the scriptSig
        opcode = int(scriptsig[0:2], 16)
        
        # Handle different push opcodes
        if 1 <= opcode <= 0x4b:
            # Direct push: opcode is the length
            length = opcode
            if len(scriptsig) < 2 + length * 2:
                return None
            height_hex = scriptsig[2:2 + length * 2]
            
        elif opcode == 0x4c:  # OP_PUSHDATA1
            if len(scriptsig) < 4:
                return None
            length = int(scriptsig[2:4], 16)
            if len(scriptsig) < 4 + length * 2:
                return None
            height_hex = scriptsig[4:4 + length * 2]
            
        elif opcode == 0x4d:  # OP_PUSHDATA2
            if len(scriptsig) < 6:
                return None
            # Length is 2 bytes, little-endian
            length_bytes = bytes.fromhex(scriptsig[2:6])
            length = int.from_bytes(length_bytes, byteorder='little')
            if len(scriptsig) < 6 + length * 2:
                return None
            height_hex = scriptsig[6:6 + length * 2]
            
        elif opcode == 0x4e:  # OP_PUSHDATA4
            if len(scriptsig) < 10:
                return None
            # Length is 4 bytes, little-endian
            length_bytes = bytes.fromhex(scriptsig[2:10])
            length = int.from_bytes(length_bytes, byteorder='little')
            if len(scriptsig) < 10 + length * 2:
                return None
            height_hex = scriptsig[10:10 + length * 2]
            
        else:
            # Not a push opcode or OP_0
            return None
        
        # Convert height from little-endian bytes to integer
        if len(height_hex) == 0:
            return None
            
        height_bytes = bytes.fromhex(height_hex)
        height = int.from_bytes(height_bytes, byteorder='little', signed=False)
        
        return height
        
    except Exception as e:
        print(f"Warning: Could not extract height from coinbase: {e}", file=sys.stderr)
        return None


def bech32_polymod(values):
    """Internal function for Bech32 checksum"""
    GEN = [0x3b6a57b2, 0x26508e6d, 0x1ea119fa, 0x3d4233dd, 0x2a1462b3]
    chk = 1
    for value in values:
        b = chk >> 25
        chk = (chk & 0x1ffffff) << 5 ^ value
        for i in range(5):
            chk ^= GEN[i] if ((b >> i) & 1) else 0
    return chk


def bech32_hrp_expand(hrp):
    """Expand the HRP into values for checksum computation"""
    return [ord(x) >> 5 for x in hrp] + [0] + [ord(x) & 31 for x in hrp]


def bech32_create_checksum(hrp, data):
    """Compute the checksum values given HRP and data"""
    values = bech32_hrp_expand(hrp) + data
    polymod = bech32_polymod(values + [0, 0, 0, 0, 0, 0]) ^ 1
    return [(polymod >> 5 * (5 - i)) & 31 for i in range(6)]


def bech32_encode(hrp, witver, witprog):
    """Encode a segwit address"""
    charset = "qpzry9x8gf2tvdw0s3jn54khce6mua7l"
    data = [witver] + convertbits(witprog, 8, 5)
    checksum = bech32_create_checksum(hrp, data)
    return hrp + '1' + ''.join([charset[d] for d in data + checksum])


def convertbits(data, frombits, tobits, pad=True):
    """Convert between bit groups"""
    acc = 0
    bits = 0
    ret = []
    maxv = (1 << tobits) - 1
    max_acc = (1 << (frombits + tobits - 1)) - 1
    for value in data:
        acc = ((acc << frombits) | value) & max_acc
        bits += frombits
        while bits >= tobits:
            bits -= tobits
            ret.append((acc >> bits) & maxv)
    if pad:
        if bits:
            ret.append((acc << (tobits - bits)) & maxv)
    elif bits >= frombits or ((acc << (tobits - bits)) & maxv):
        return None
    return ret


def segwit_addr_encode(hrp, witver, witprog_hex):
    """Encode a SegWit address from hex witness program"""
    witprog = bytes.fromhex(witprog_hex)
    return bech32_encode(hrp, witver, list(witprog))


def base58_encode(hex_string: str) -> str:
    """Encode a hex string to Base58"""
    alphabet = "123456789ABCDEFGHJKLMNPQRSTUVWXYZabcdefghijkmnopqrstuvwxyz"
    num = int(hex_string, 16)
    encoded = ""
    while num > 0:
        num, remainder = divmod(num, 58)
        encoded = alphabet[remainder] + encoded
    # Add leading 1s for leading 00 bytes
    for i in range(0, len(hex_string), 2):
        if hex_string[i:i+2] == "00":
            encoded = "1" + encoded
        else:
            break
    return encoded


def pubkey_hash_to_address(pubkey_hash: str, version_byte: str = "00") -> str:
    """Convert a public key hash to a Bitcoin address using Base58Check encoding"""
    # Add version byte (0x00 for mainnet P2PKH, 0x05 for P2SH)
    versioned = version_byte + pubkey_hash
    
    # Double SHA256 for checksum
    hash1 = hashlib.sha256(bytes.fromhex(versioned)).digest()
    hash2 = hashlib.sha256(hash1).digest()
    checksum = hash2[:4].hex()
    
    # Combine and encode
    address_hex = versioned + checksum
    return base58_encode(address_hex)


def extract_addresses_from_coinbase(coinbase_part2: str) -> List[Dict[str, Any]]:
    """
    Extract Bitcoin addresses from coinbase transaction outputs.
    
    coinbase_part2 may contain:
    - scriptSig continuation (variable length)
    - 4 bytes: sequence number
    - (Optional for SegWit) 1 byte: marker (0x00) + 1 byte: flag (0x01)
    - varint: number of outputs
    - outputs (each has value + scriptPubKey)
    - (Optional for SegWit) witness data
    - 4 bytes: locktime
    
    Note: Stratum splits the coinbase where the miner inserts extranonce,
    so part2 may start with scriptSig continuation data. We search for the
    sequence marker (0xffffffff) to find where outputs begin.
    """
    outputs = []
    
    try:
        coinbase_hex = coinbase_part2.strip()
        
        if len(coinbase_hex) < 10:
            return outputs
        
        offset = 0
        
        # Search for sequence marker (0xffffffff) followed by output count
        # Common patterns: ffffffff + 01/02/03 (1-3 outputs)
        # The challenge is that "ffffffff" might appear in scriptSig data
        # So we look for ffffffff followed by a plausible number of outputs (01-10)
        
        offset = 0
        found_sequence = False
        
        for i in range(len(coinbase_hex) - 10):
            if coinbase_hex[i:i+8] == "ffffffff":
                # Check if next byte looks like a valid output count (1-10)
                next_byte = coinbase_hex[i+8:i+10]
                if next_byte and int(next_byte, 16) in range(1, 11):
                    # This looks like the sequence!
                    offset = i + 8
                    found_sequence = True
                    break
        
        if not found_sequence:
            # Try simpler approach: part2 starts with sequence
            if coinbase_hex.startswith("ffffffff"):
                offset = 8
            elif coinbase_hex.startswith("01340000") or coinbase_hex.startswith("00000000"):
                # Might be a non-standard sequence at start
                offset = 8
            else:
                # Can't find sequence, give up
                return outputs
        
        # Check for SegWit marker and flag
        if offset < len(coinbase_hex) - 4:
            marker = coinbase_hex[offset:offset+2]
            
            # Determine if this is a witness transaction
            # If marker is 0x00 and next byte (flag) is 0x01, it's witness
            if marker == "00" and len(coinbase_hex) > offset + 2:
                flag = coinbase_hex[offset+2:offset+4]
                if flag in ["00", "01"]:
                    # SegWit transaction
                    offset += 4
        
        # Read number of outputs
        if len(coinbase_hex) < offset + 2:
            return outputs
            
        num_outputs = int(coinbase_hex[offset:offset+2], 16)
        offset += 2
        
        # Parse each output
        for i in range(num_outputs):
            if len(coinbase_hex) < offset + 16:
                break
                
            # Value (8 bytes, little-endian satoshis)
            value_hex = coinbase_hex[offset:offset+16]
            value_bytes = bytes.fromhex(value_hex)
            value_satoshis = int.from_bytes(value_bytes, byteorder='little')
            offset += 16
            
            # ScriptPubKey length
            if len(coinbase_hex) < offset + 2:
                break
            script_len = int(coinbase_hex[offset:offset+2], 16)
            offset += 2
            
            # ScriptPubKey
            if len(coinbase_hex) < offset + script_len * 2:
                break
            script_pubkey = coinbase_hex[offset:offset+script_len*2]
            offset += script_len * 2
            
            # Parse address based on script type
            output_info = {
                'value_satoshis': value_satoshis,
                'value_btc': value_satoshis / 100000000,
                'script_pubkey': script_pubkey,
                'address': None,
                'type': 'Unknown'
            }
            
            # P2PKH: OP_DUP OP_HASH160 <20 bytes> OP_EQUALVERIFY OP_CHECKSIG
            if script_pubkey.startswith("76a914") and script_pubkey.endswith("88ac") and len(script_pubkey) == 50:
                pubkey_hash = script_pubkey[6:46]
                output_info['type'] = 'P2PKH'
                output_info['address'] = pubkey_hash_to_address(pubkey_hash, "00")
            
            # P2SH: OP_HASH160 <20 bytes> OP_EQUAL
            elif script_pubkey.startswith("a914") and script_pubkey.endswith("87") and len(script_pubkey) == 46:
                script_hash = script_pubkey[4:44]
                output_info['type'] = 'P2SH'
                output_info['address'] = pubkey_hash_to_address(script_hash, "05")
            
            # P2WPKH: OP_0 <20 bytes>
            elif script_pubkey.startswith("0014") and len(script_pubkey) == 44:
                witness_program = script_pubkey[4:]
                output_info['type'] = 'P2WPKH'
                output_info['address'] = segwit_addr_encode("bc", 0, witness_program)
            
            # P2WSH: OP_0 <32 bytes>
            elif script_pubkey.startswith("0020") and len(script_pubkey) == 68:
                witness_program = script_pubkey[4:]
                output_info['type'] = 'P2WSH'
                output_info['address'] = segwit_addr_encode("bc", 0, witness_program)
            
            # OP_RETURN (null data)
            elif script_pubkey.startswith("6a"):
                output_info['type'] = 'OP_RETURN'
                output_info['address'] = '(Null Data)'
            
            outputs.append(output_info)
        
        return outputs
        
    except Exception as e:
        print(f"Warning: Could not extract addresses from coinbase: {e}", file=sys.stderr)
        return outputs


def parse_mining_notify(notify_data: Any) -> Dict[str, Any]:
    """
    Parse a Stratum mining.notify message.
    
    mining.notify params format:
    [
        job_id,              # 0: Job ID
        prevhash,            # 1: Previous block hash (little-endian)
        coinbase_part1,      # 2: Coinbase part 1
        coinbase_part2,      # 3: Coinbase part 2
        merkle_branches,     # 4: List of merkle branches
        version,             # 5: Block version
        nbits,               # 6: Difficulty bits
        ntime,               # 7: Current time
        clean_jobs           # 8: Clean jobs flag
    ]
    """
    result = {}
    
    # Handle both raw params array and full JSON-RPC message
    if isinstance(notify_data, dict):
        if 'params' in notify_data:
            params = notify_data['params']
        else:
            raise ValueError("Invalid format: expected 'params' in dict")
    elif isinstance(notify_data, list):
        params = notify_data
    else:
        raise ValueError("Invalid format: expected dict or list")
    
    if len(params) < 9:
        raise ValueError(f"Invalid mining.notify: expected at least 9 parameters, got {len(params)}")
    
    # Extract fields
    result['job_id'] = params[0]
    
    # Previous hash (convert from little-endian to big-endian for display)
    prevhash_le = params[1]
    result['prevhash_le'] = prevhash_le
    result['prevhash'] = reverse_hex(prevhash_le)
    
    # Try to extract block height from coinbase
    coinbase_part1 = params[2]
    height = extract_height_from_coinbase(coinbase_part1)
    result['height'] = height
    
    # Extract addresses from coinbase outputs
    coinbase_part2 = params[3]
    outputs = extract_addresses_from_coinbase(coinbase_part2)
    result['outputs'] = outputs
    
    # Additional fields
    result['version'] = params[5]
    result['nbits'] = params[6]
    result['ntime'] = params[7]
    result['clean_jobs'] = params[8]
    
    return result


def main():
    """Main function to parse Stratum mining.notify strings"""
    
    if len(sys.argv) > 1:
        # Parse from command line argument
        input_str = sys.argv[1]
    else:
        # Read from stdin
        print("Enter Stratum mining.notify JSON (or Ctrl+D to exit):")
        print("Example format: {\"method\":\"mining.notify\",\"params\":[...]}")
        print()
        input_str = sys.stdin.read().strip()
    
    if not input_str:
        print("Error: No input provided", file=sys.stderr)
        print("\nUsage:")
        print("  python stratum_parser.py '<json_string>'")
        print("  or")
        print("  echo '<json_string>' | python stratum_parser.py")
        sys.exit(1)
    
    try:
        # Try to parse as JSON
        data = json.loads(input_str)
        result = parse_mining_notify(data)
        
        # Display results
        print("=" * 70)
        print("STRATUM MINING.NOTIFY PARSED DATA")
        print("=" * 70)
        print(f"Job ID:           {result['job_id']}")
        print(f"Block Height:     {result['height'] if result['height'] else 'Unable to extract'}")
        print(f"Previous Hash:    {result['prevhash']}")
        print(f"Block Version:    {result['version']}")
        print(f"Difficulty (nBits): {result['nbits']}")
        
        # Convert ntime to human-readable timestamp
        ntime_int = int(result['ntime'], 16)
        ntime_date = datetime.fromtimestamp(ntime_int).strftime('%Y-%m-%d %H:%M:%S UTC')
        print(f"Timestamp (nTime): {result['ntime']} ({ntime_date})")
        
        print(f"Clean Jobs:       {result['clean_jobs']}")
        
        # Display coinbase outputs and addresses
        if result.get('outputs'):
            print()
            print("Coinbase Outputs:")
            for i, output in enumerate(result['outputs'], 1):
                print(f"  Output {i}:")
                print(f"    Value:   {output['value_btc']:.8f} BTC ({output['value_satoshis']:,} satoshis)")
                print(f"    Type:    {output['type']}")
                if output['address']:
                    print(f"    Address: {output['address']}")
        
        print("=" * 70)
        
    except json.JSONDecodeError as e:
        print(f"Error: Invalid JSON format: {e}", file=sys.stderr)
        sys.exit(1)
    except ValueError as e:
        print(f"Error: {e}", file=sys.stderr)
        sys.exit(1)
    except Exception as e:
        print(f"Error: Unexpected error: {e}", file=sys.stderr)
        sys.exit(1)


if __name__ == "__main__":
    main()
