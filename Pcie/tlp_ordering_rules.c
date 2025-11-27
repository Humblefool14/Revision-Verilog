#include <stdint.h>
#include <stdbool.h>
#include <assert.h>

/* PCIe TLP Types */
typedef enum {
    TLP_POSTED_REQUEST,
    TLP_READ_REQUEST,
    TLP_NPR_WITH_DATA,  /* Non-Posted Request with Data */
    TLP_COMPLETION
} tlp_type_t;

/* TLP Attributes */
typedef struct {
    tlp_type_t type;
    bool ro_set;        /* Relaxed Ordering */
    bool ido_set;       /* ID-based Ordering */
    uint16_t requester_id;
    uint16_t completer_id;
    uint32_t pasid_tlp_prefix;  /* PASID TLP Prefix value */
    bool has_pasid;
    uint32_t transaction_id;    /* For tracking completions */
} tlp_t;

/* Ordering Rules Matrix - [row_passes_column]
 * Based on Table 2-40 from PCIe Spec 5.0
 * true = can pass, false = cannot pass (must maintain order)
 */
static const bool ordering_matrix[4][4] = {
    /*                  Posted  Read   NPR    Compl */
    /* Posted    */ {   false,  true,  true,  true  },
    /* Read      */ {   false,  true,  true,  true  },
    /* NPR       */ {   false,  true,  true,  true  },
    /* Completion*/ {   false,  true,  true,  true  }
};

/* Helper function to check if two requesters are different */
static inline bool different_requesters(const tlp_t *t1, const tlp_t *t2) {
    return t1->requester_id != t2->requester_id;
}

/* Helper function to check PASID difference */
static inline bool different_pasid(const tlp_t *t1, const tlp_t *t2) {
    if (!t1->has_pasid || !t2->has_pasid)
        return false;
    return t1->pasid_tlp_prefix != t2->pasid_tlp_prefix;
}

/* Rule A2a: Posted Request cannot pass another Posted Request unless A2b applies */
static inline bool check_rule_A2a(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_POSTED_REQUEST || blocking->type != TLP_POSTED_REQUEST)
        return true;  /* Rule doesn't apply */
    
    /* Must check A2b exceptions before failing */
    return false;  /* Default: cannot pass */
}

/* Rule A2b: Posted can pass Posted with RO or IDO exceptions */
static inline bool check_rule_A2b(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_POSTED_REQUEST || blocking->type != TLP_POSTED_REQUEST)
        return false;  /* Exception doesn't apply */
    
    /* Exception 1: RO set */
    if (passing->ro_set)
        return true;
    
    /* Exception 2: IDO set with different requester IDs or different PASID */
    if (passing->ido_set && (different_requesters(passing, blocking) || 
                             different_pasid(passing, blocking)))
        return true;
    
    return false;
}

/* Rule A3, A4: Posted Request must be able to pass Non-Posted Requests */
static inline bool check_rule_A3_A4(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_POSTED_REQUEST)
        return true;  /* Rule doesn't apply */
    
    if (blocking->type == TLP_READ_REQUEST || blocking->type == TLP_NPR_WITH_DATA)
        return true;  /* Must be able to pass */
    
    return true;
}

/* Rule A5a: Posted can pass Completion (not required unless A5b) */
static inline bool check_rule_A5a(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_POSTED_REQUEST || blocking->type != TLP_COMPLETION)
        return true;  /* Rule doesn't apply */
    
    return true;  /* Permitted but not required */
}

/* Rule B2a: Read Request cannot pass Posted Request unless B2b applies */
static inline bool check_rule_B2a(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_READ_REQUEST || blocking->type != TLP_POSTED_REQUEST)
        return true;  /* Rule doesn't apply */
    
    return false;  /* Cannot pass unless B2b */
}

/* Rule B2b: Read can pass Posted with IDO exceptions */
static inline bool check_rule_B2b(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_READ_REQUEST || blocking->type != TLP_POSTED_REQUEST)
        return false;  /* Exception doesn't apply */
    
    if (passing->ido_set && (different_requesters(passing, blocking) || 
                             different_pasid(passing, blocking)))
        return true;
    
    return false;
}

/* Rule C2a: NPR with Data cannot pass Posted Request unless C2b applies */
static inline bool check_rule_C2a(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_NPR_WITH_DATA || blocking->type != TLP_POSTED_REQUEST)
        return true;  /* Rule doesn't apply */
    
    return false;  /* Cannot pass unless C2b */
}

/* Rule C2b: NPR with Data can pass Posted with RO or IDO exceptions */
static inline bool check_rule_C2b(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_NPR_WITH_DATA || blocking->type != TLP_POSTED_REQUEST)
        return false;  /* Exception doesn't apply */
    
    /* Exception 1: RO set */
    if (passing->ro_set)
        return true;
    
    /* Exception 2: IDO set with different requester IDs or different PASID */
    if (passing->ido_set && (different_requesters(passing, blocking) || 
                             different_pasid(passing, blocking)))
        return true;
    
    return false;
}

/* Rule B3, B4, C3, C4: Non-Posted can pass another Non-Posted */
static inline bool check_rule_B3_B4_C3_C4(const tlp_t *passing, const tlp_t *blocking) {
    bool passing_is_npr = (passing->type == TLP_READ_REQUEST || 
                           passing->type == TLP_NPR_WITH_DATA);
    bool blocking_is_npr = (blocking->type == TLP_READ_REQUEST || 
                            blocking->type == TLP_NPR_WITH_DATA);
    
    if (passing_is_npr && blocking_is_npr)
        return true;  /* Can pass */
    
    return true;  /* Rule doesn't apply */
}

/* Rule B5, C5: Non-Posted can pass Completion */
static inline bool check_rule_B5_C5(const tlp_t *passing, const tlp_t *blocking) {
    bool passing_is_npr = (passing->type == TLP_READ_REQUEST || 
                           passing->type == TLP_NPR_WITH_DATA);
    
    if (passing_is_npr && blocking->type == TLP_COMPLETION)
        return true;  /* Can pass */
    
    return true;  /* Rule doesn't apply */
}

/* Rule D2a: Completion cannot pass Posted Request unless D2b applies */
static inline bool check_rule_D2a(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_COMPLETION || blocking->type != TLP_POSTED_REQUEST)
        return true;  /* Rule doesn't apply */
    
    return false;  /* Cannot pass unless D2b */
}

/* Rule D2b: Completion can pass Posted with RO, IDO, or different completer */
static inline bool check_rule_D2b(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_COMPLETION || blocking->type != TLP_POSTED_REQUEST)
        return false;  /* Exception doesn't apply */
    
    /* Exception 1: I/O or Config Write Completion (special completion types) */
    /* Exception 2: RO set */
    if (passing->ro_set)
        return true;
    
    /* Exception 3: IDO set with different completer/requester */
    if (passing->ido_set && passing->completer_id != blocking->requester_id)
        return true;
    
    return false;
}

/* Rule D3, D4: Completion must be able to pass Non-Posted Requests */
static inline bool check_rule_D3_D4(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_COMPLETION)
        return true;  /* Rule doesn't apply */
    
    if (blocking->type == TLP_READ_REQUEST || blocking->type == TLP_NPR_WITH_DATA)
        return true;  /* Must be able to pass */
    
    return true;
}

/* Rule D5a: Completions with different Transaction IDs can pass each other */
static inline bool check_rule_D5a(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_COMPLETION || blocking->type != TLP_COMPLETION)
        return true;  /* Rule doesn't apply */
    
    if (passing->transaction_id != blocking->transaction_id)
        return true;  /* Can pass */
    
    return true;
}

/* Rule D5b: Completions with same Transaction ID cannot pass each other */
static inline bool check_rule_D5b(const tlp_t *passing, const tlp_t *blocking) {
    if (passing->type != TLP_COMPLETION || blocking->type != TLP_COMPLETION)
        return true;  /* Rule doesn't apply */
    
    if (passing->transaction_id == blocking->transaction_id)
        return false;  /* Cannot pass - maintains address order */
    
    return true;
}

/* Main ordering check function */
bool can_tlp_pass(const tlp_t *passing, const tlp_t *blocking) {
    /* First check base matrix */
    bool base_can_pass = ordering_matrix[passing->type][blocking->type];
    
    /* If base says cannot pass, check for exceptions */
    if (!base_can_pass) {
        /* Check A2b exception for Posted-Posted */
        if (check_rule_A2b(passing, blocking))
            return true;
        
        /* Check B2b exception for Read-Posted */
        if (check_rule_B2b(passing, blocking))
            return true;
        
        /* Check C2b exception for NPR-Posted */
        if (check_rule_C2b(passing, blocking))
            return true;
        
        /* Check D2b exception for Completion-Posted */
        if (check_rule_D2b(passing, blocking))
            return true;
        
        /* No exceptions apply */
        return false;
    }
    
    /* Check D5b - same transaction ID completions cannot pass */
    if (!check_rule_D5b(passing, blocking))
        return false;
    
    return true;
}

/* Assert-style macros for testing */
#define ASSERT_CAN_PASS(passing, blocking) \
    assert(can_tlp_pass(passing, blocking) && \
           "TLP ordering violation: passing TLP cannot pass blocking TLP")

#define ASSERT_CANNOT_PASS(passing, blocking) \
    assert(!can_tlp_pass(passing, blocking) && \
           "TLP ordering violation: passing TLP should not be able to pass blocking TLP")

/* Test function demonstrating usage */
void test_ordering_rules(void) {
    tlp_t posted1 = {TLP_POSTED_REQUEST, false, false, 0x1234, 0, 0, false, 0};
    tlp_t posted2 = {TLP_POSTED_REQUEST, false, false, 0x5678, 0, 0, false, 0};
    tlp_t posted_ro = {TLP_POSTED_REQUEST, true, false, 0x1234, 0, 0, false, 0};
    tlp_t read = {TLP_READ_REQUEST, false, false, 0x1234, 0, 0, false, 0};
    tlp_t completion = {TLP_COMPLETION, false, false, 0, 0x1234, 0, false, 1};
    
    /* Test A2a: Posted cannot pass Posted (without exceptions) */
    ASSERT_CANNOT_PASS(&posted1, &posted2);
    
    /* Test A2b: Posted with RO can pass Posted */
    ASSERT_CAN_PASS(&posted_ro, &posted2);
    
    /* Test A3: Posted can pass Read */
    ASSERT_CAN_PASS(&posted1, &read);
    
    /* Test B2a: Read cannot pass Posted (without exceptions) */
    ASSERT_CANNOT_PASS(&read, &posted1);
    
    /* Test D5b: Completions with same transaction ID cannot pass */
    tlp_t comp1 = {TLP_COMPLETION, false, false, 0, 0x1234, 0, false, 1};
    tlp_t comp2 = {TLP_COMPLETION, false, false, 0, 0x1234, 0, false, 1};
    ASSERT_CANNOT_PASS(&comp1, &comp2);
}