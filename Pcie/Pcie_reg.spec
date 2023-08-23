module PCIE {
    registerArray VENDOR{
    displayName = "NPEM register"
    description = "NPEM register"
    length = 'd1
    addressOffset = 'h0
    size = 'd32
    volatile = false
    fields[
      field ID{
        description = ""
        bitOffset = 'd0
        reset='d0
        bitWidth='d32
        access = RO
      }
    ]
  }
  
  registerArray DEV{
    displayName = "Device ID register"
    description = "Device ID register"
    length = 'd1
    addressOffset = 'h0
    size = 'd32
    volatile = false
    fields[
      field ID{
        description = ""
        bitOffset = 'd0
        reset='d0
        bitWidth='d32
        access = RO
      }
    ]
  }
  registerArray EXPR_CAP_LIST{
    displayName = "NPEM register"
    description = "NPEM register"
    length = 'd1
    addressOffset = 'h0
    size = 'd32
    volatile = false
    fields[
      field EXT_CAP_ID{
        description = "divr of pll"
        bitOffset = 'd0
        reset='d0
        bitWidth='d8
        access = RO
      }
      field NXT_CAP_PTR{
        description = "address"
        bitOffset = 'd8
        reset='d1
        bitWidth='d8
        access = RO
      }
      field CAPA_VER{
        description = "address"
        bitOffset = 'd15
        reset='d1
        bitWidth='d4
        access = RO
      }
    ]
  }
  registerArray NPEM_CFG0{
    displayName = "NPEM register"
    description = "NPEM register"
    length = 'd1
    addressOffset = 'h0
    size = 'd32
    volatile = false
    fields[
      field EXTENDED_CAP_ID{
        description = "divr of pll"
        bitOffset = 'd0
        reset='d0
        bitWidth='d15
        access = RO
      }
      field CAP_VER{
        description = "address"
        bitOffset = 'd16
        reset='d1
        bitWidth='d4
        access = RW
      }
      field NXT_CAP{
        description = "address"
        bitOffset = 'd20
        reset='d11
        bitWidth='d4
        access = RO
      }
    ]
  }
}
