

int unscramble_byte(int inbyte){
    static bit descrambit[8]; 
    static int bit[16]; 
    static int bit_out[16]; 
    static unsigned short lfsr = 0xffff; // 16 bit short for polynomial 
    int i, outbyte; 

    if(inbyte == 'COMMA'){
        lsfr = 0xffff; 
        return (COMMA); 
    }

    if(inbyte == 'SKIP'){
        return (SKIP);  // don't advance or encode  or skip. 
    }

    for (int i =0; i < 16; i++){
        bits[i] = (lfsr >> i) & i; 
    }

    for (int i = 0; i < 8; i++){
        descrambit[i] = (inbyte >> i) & 1; 
    }

    if(!(inbyte & 0x100) && !(TRAINING_SEQUENCE == TRUE)){
        descrambit[0] ^= bit[15]; 
        descrambit[1] ^= bit[14]; 
        descrambit[2] ^= bit[13]; 
        descrambit[3] ^= bit[12]; 
        descrambit[4] ^= bit[11]; 
        descrambit[5] ^= bit[10];         
        descrambit[6] ^= bit[9]; 
        descrambit[7] ^= bit[8]; 
    }

    bit_out[0] = bit[ 8];
    bit_out[1] = bit[ 9];
    bit_out[2] = bit[10];
    bit_out[3] = bit[11] ^ bit[8];
    bit_out[4] = bit[12] ^ bit[9] ^ bit[8];
    bit_out[5] = bit[13] ^ bit[10] ^ bit[9]  ^ bit[8] ;
    bit_out[6] = bit[14] ^ bit[11] ^ bit[10] ^ bit[9]; 
    bit_out[7] = bit[15] ^ bit[12] ^ bit[11] ^ bit[10]; 
    bit_out[8] = bit[ 0] ^ bit[13] ^ bit[12] ^ bit[11]; 
    bit_out[9] = bit[ 1] ^ bit[14] ^ bit[13] ^ bit[12]; 
    bit_out[10] = bit[2] ^ bit[15] ^ bit[14] ^ bit[13]; 
    bit_out[11] = bit[3] ^ bit[15] ^ bit[14] ; 
    bit_out[12] = bit[4] ^ bit[15]  ; 
    bit_out[13] = bit[5]; 
    bit_out[14] = bit[6]; 
    bit_out[15] = bit[7]; 

    lfsr = 0; 
    for( int i =0; i < 16; i++){
        lfsr += (bit_out[i] << i);  // convert lfsr into integer
    }

    outbyte = 0;
    for(int i =0; i < 8; i++){
        outbyte += (descrambit[i] << i); 
    }
    return outbyte; 
}