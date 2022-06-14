# Reviews

Previous reviews of Wenhao's paper


# TL;DR

## Differences Between PoBF and Liveries

- Not an CFI-based solution -> no instrumentation and its overhead
- Machine-checked proof
- Not designed only for SGX

## Weakness of Liveries

- Incomplete/informal verification
- Potentially incorrect use of cryptography
- Unexplained performance enhancement/degradation
- The service/threat model and the motivation are not clear
- Lack of experimentation on systems issues: **concurrency** and context switching
- Where data is located and loaded is note clear
- Side-channel
- The proof is infomral
- Compatibility to software and SGX2

## Insights

- Evaluation with reak world apps (e.g., ML)
- Why this service model is useful
- 

# TDSC 2022

## Editor Comments

Associate Editor
Comments to the Author:
Thank you for your submission. Based on the reviewer comments, particularly given that there was a desire to see further evaluation, the paper has been assigned a major review decision. Please read through the comments from the reviewers in detail, in particularly relating to the utility of the proof and the additional experimentation required.


## Reviewer Comments

Please note that some reviewers may have included additional comments in a separate file. If a review contains the note "see the attached file" under Section III A - Public Comments, you will need to log on to ScholarOne Manuscripts  to view the file. After logging in, select the Author Center, click on the "Manuscripts with Decisions" queue and then clicking on the "view decision letter" link for this manuscript. You must scroll down to the very bottom of the letter to see the file(s), if any.  This will open the file that the reviewer(s) or the Associate Editor included for you along with their review.

### Reviewer: 1

Recommendation: Author Should Prepare A Minor Revision

#### Comments:
This paper proposes a lightweight and verifiable method for users isolation in supporting in-enclave services. This work makes extensive experiments to demonstrate the efficiency and the small TCB size of the method.
 
#### Strengths
- The first lightweight and verifiable isolation solution for in-enclave multi-user services.
- Some practical improvements over prior work.
 
#### Weaknesses

- The description of Sblock examples in Fig. 1 is confused, we suggest the authors add more detailed instructions according to the definition.
- Some background knowledge should be introduced to help to understand the method. For example, the authors did not describe the specifics of ENCLU, EGETKEY and EREPORT leaf functions, which are important for the design.
- In Section 7.2, the experiment uses Intel Xeon E3-1585Lv5 CPU. Does this CPU support SGX hardware mode? The authors should declare which mode of SGX is used in the experiment.
- In the experiments, the authors use a small CNN model with 8 hidden layers and use a small batch size. Does the system support the more practical CNN like ResNet.

#### Additional Questions:

1.  Please explain how this manuscript advances this field of research and/or contributes something new to the literature.: The prior works about in-enclave sandbox are used to sandbox concurrent tasks within an enclave by software fault isolation (SFI). This paper is for lightweight user isolation
under the sequential service model, which brings in advantages such as low performance/memory overhead and
extremely small TCB for the protection verifiable.

2. Is the manuscript technically sound? Please explain your answer under Public Comments below.: Yes

1. Which category describes this manuscript?: Research/Technology

2. How relevant is this manuscript to the readers of this periodical? Please explain your rating under Public Comments below.: Very Relevant

1. Are the title, abstract, and keywords appropriate? Please explain under Public Comments below.: Yes

2. Does the manuscript contain sufficient and appropriate references? Please explain under Public Comments below.: References are sufficient and appropriate

3. Does the introduction state the objectives of the manuscript in terms that encourage the reader to read on? Please explain your answer under Public Comments below.: Yes

4. How would you rate the organization of the manuscript? Is it focused? Is the length appropriate for the topic? Please explain under Public Comments below.: Could be improved

5. Please rate the readability of the manuscript. Explain your rating under Public Comments below.: Readable - but requires some effort to understand

6. Should the supplemental material be included? (Click on the Supplementary Files icon to view files): Yes, as part of the main paper if accepted (cannot exceed the strict page limit)

7. If yes to 6, should it be accepted: As is

Please rate the manuscript. Explain your choice: Excellent


### Reviewer: 2

Recommendation: Author Should Prepare A Minor Revision

#### Comments: 

The paper addresses an interesting problem - reducing the overhead of starting an enclave when used by multiple users.  The approach seems sound, but there are some issues that need be addressed.
 
My main gripe is that the paper claims to prove the correctness of the security configuration and to verify the implementation.  Yet, the only "proof" in the paper is for Theorem 1, which only covers a small part of the proposed security mechanism, is too vague to be a real theorem, and consequently the proof is more of a hand-wavy argument for correctness. To become a real theorem, the paper needs a better definition of the terms and assumptions upon which the theorem is built. I doubt that a meaningful proof can be done within the scope of the paper and suggest that the authors drop the claim of proven security.
 
Similarly, the verification makes a large number of hidden assumptions that are not properly outlined and I doubt they hold.  In particular, the verification example in Fig 6 assumes atomicity of the code of sgx_ra_get_ga w.r.t. attackers 1 and 2.  However, the operating system can exhaust the rdrand entropy while the sblock is running.  While I agree that such an attack would be successful and hence do not think it affects the security of Liveries, the attack breaks the model used for verification.  The paper should do a much better job at specifying the assumptions for the verification and convincing why they are reasonable.
 
The protocol used by the users for reconnection is not clear.  Section 3.1 claims that a session key is securely stored in the enclave.  However, the protocol and the details of protection are vague.  I assume that the key is encrypted with an enclave key and is only accessed while communicating with the user.  However, there is a need to first show the protocol and second to show the sblocks used for key access.  Also, what protects the key against DoS attacks, where a malicious user modifies the key of another user to prevent access?
 
The main motivation for Liveries is enclaves with large amount of data ("gigabytes of model parameters" P4L46L).  Yet, the largest evaluation is on enclaves with 256MB of data, and most of the evaluation is on significantly smaller models.
 
I suggest replacing the code in Fig 4 and others with pseudocode.  I do not see the benefit of showing the C API in all its gory details.
 
It seems that Liveries may be vulnerable to model roll-back attacks where the attacker installs an older version of the model which is correctly signed by the service provider.  I suggest discussing this.
 
I suggest relating Section 5 back to the policies P0-P5 introduced in Section 4.
 
P10L3L - I am not sure i understand the problem with EGETKEY and EREPORT.  I thought these were only running in an sblock, which the paper earlier claims to only work in single-thread mode.
 
The performance evaluation, particularly of Q2 could be improved.  First it seems that multiple parameters change between tests, making it hard to get a good picture of the results.  These include the size of TMP_AREA in various experiments and the number of measurements taken in each experiment.  Moreover, the paper should provide the raw running times, not only the overheads.  Finally, the experiments should be extended to the claimed size of gigabytes of model parameters.
 
One question re motivation is that if the user uses the service frequently, having a dedicated enclave is likely more efficient than validating the enclave for each connection.  If the user accesses the service rarely, the amortized cost of spawning a new enclave is likely to be insignificant.  As such, it would seem that having a cache of several enclave instances should be a simpler, more secure approach than Liveries.

 
#### Editorial

* P3L23R: target enclave who --> which

* P3L32R: CMAC is not defined

* P3L44R-P3L47R: words in math mode should be protected with \mathit{}

* P9L37L: SGX supports... --- Should this not be SGX2?


 
ManuscriptCentral is one of the worst reviewing systems around.  My apologies for any formatting issues in this review.

#### Additional Questions:

1.  Please explain how this manuscript advances this field of research and/or contributes something new to the literature.: The paper proposes Liveries - an approach to safely share an SGX enclave by multiple users.  Liveries enforces that only a single user can use the enclave at each time and ensures that the state is sanitized when switching users.  Liveries is based on the idea of sblocks, which are "atomic" sequences of instructions used to perform sensitive operations, including state sanitization and operations with secret data.  The atomicity of sblocks and prevention of sensitive operations outside them are ensured via static analysis to remove sensitive instructions from the code.

2. Is the manuscript technically sound? Please explain your answer under Public Comments below.: Yes

1. Which category describes this manuscript?: Research/Technology

2. How relevant is this manuscript to the readers of this periodical? Please explain your rating under Public Comments below.: Very Relevant

1. Are the title, abstract, and keywords appropriate? Please explain under Public Comments below.: Yes

2. Does the manuscript contain sufficient and appropriate references? Please explain under Public Comments below.: References are sufficient and appropriate

3. Does the introduction state the objectives of the manuscript in terms that encourage the reader to read on? Please explain your answer under Public Comments below.: Yes

4. How would you rate the organization of the manuscript? Is it focused? Is the length appropriate for the topic? Please explain under Public Comments below.: Satisfactory

5. Please rate the readability of the manuscript. Explain your rating under Public Comments below.: Readable - but requires some effort to understand

6. Should the supplemental material be included? (Click on the Supplementary Files icon to view files): Does not apply, no supplementary files included

7. If yes to 6, should it be accepted: After revisions.  Please include explanation under Public Comments below.

Please rate the manuscript. Explain your choice: Good


### Reviewer: 3

Recommendation: Author Should Prepare A Major Revision For A Second Review

#### Comments:

This paper introduces a thin layer within SGX enclaves to achieve a lightweight and verifiable user isolation within enclaves under the setting of a multi-user environment. Specifically, the proposed system restricts the invocation of sensitive instructions within the enclave (e.g., EGETKEY) using the concept of sblock, and regulates data access from threads and interrupts. Different user data is further encrypted in rest and cleaned up after usage. The introduced security monitor guarantees complete mediation during enclave transitions. The whole system is prototyped based on Intel SGX SDK assuming the availability of application source files. The evaluation includes TCB reduction analysis, formal verification using SMACK and Spin, and runtime evaluations using an ML framework.

+ Exploring an interesting idea of in-enclave isolation
+ TCB reduction comparing to Intel SGX SDK
+ Formal verification using SMACK and Spin

- This paper is hard to read here and there
- Unclear description of sblock
- Assume single thread and no exception
- Miss comparisons with SFI/CFI approaches and workload benchmark

I really like the idea of exploring in-enclave isolation to defend against potential threats imposed by multi-user environments, although I am not fully buying the ML inference example without a concrete attack scenario. I think this paper is designed against ForeShadow attacks and the current implementation only protects secret keys used by remote attestation. My first question is if the scope of the paper could be further clarified or even limited, instead of trying to shoot 100 birds at once. Honestly, the current writing also prevents me from having a better understanding of the paper, e.g., the scope, the idea, the implementation, etc. The whole paper right now reads like "yeah we design this but it might break in some cases but we could do this to compensate" instead of a systematic design across the whole paper.

The paper starts to lose me when sblock is defined and proved. First of all, I think it is a good idea to talk about the difference between sblock and basic block (from a program analysis perspective). Moving forward, how to find a sblock? How many sblocks are there in a code snippet? Are they unique? Do you mandate the maximum number of instructions within sblock? What do you mean by "a sequence of sblocks for protecting I_k?" What does "protecting" mean? What do you mean by "exit_j is also entry_y+1 running I_j?" The theorem and proof do not help, unfortunately. Why do you need them anyway if it is self-explained?

The usage of the term "enclave thread" also bothers me. What do you mean by this? Because SGX enclave does not support creating threads within enclaves, unless you are referring to user-space threading within enclaves, there is no such a thing called "enclave thread" but threads accessing enclaves. There are also multiple places where further explanation would help clarify things. E.g., "The enclave exception handler is checked..." How? "We confirmed that the enclave crashes..." So does this mean the system will not be able to remove TCS occasionally? In the end, it is still not clear to me if the whole system is built upon source file or binary analysis or both -- the first part of the paper talks about binary rewriting; later acknowledges the assumption of source files; evaluation talks about binary rewriting again. Confusing. I recommend putting more time and effort into writing to clarify things.

The constraints imposed by the system, a.k.a., single thread, no exception, and usage of GS should be mitigated. I think the paper has mentioned only to disable exception handling during sblock execution, which is good. A single thread might be a must. But please mention why a single thread might be desired (considering threats imposed by hyperthreading and side channels). GS is used by libOS approaches, e.g., GrapheneSGX. Make sure you talk about this in the paper as well.

Last, I think the evaluation should be improved. Since this paper compares against SFI/CFI approaches, it makes sense to evaluate some of these solutions if possible. Moreover, I think the workload benchmark is missing. For example, Table 9 lists a number of SGX projects. To me, having runtime overhead evaluation is more useful than counting the number of gadgets. I think the existing SGX benchmark should also help (lmbench-sgx and nbenck-sgx). I am also hoping to see the performance impact of limiting multi-thread support to a single thread, as well as exception handlings.

#### Additional Questions:

1.  Please explain how this manuscript advances this field of research and/or contributes something new to the literature.: This paper explores in-enclave isolation trying to protect enclaves under the multi-user setting, which has not been widely explored.

2. Is the manuscript technically sound? Please explain your answer under Public Comments below.: Appears to be - but didn't check completely

1. Which category describes this manuscript?: Research/Technology

2. How relevant is this manuscript to the readers of this periodical? Please explain your rating under Public Comments below.: Very Relevant

1. Are the title, abstract, and keywords appropriate? Please explain under Public Comments below.: Yes

2. Does the manuscript contain sufficient and appropriate references? Please explain under Public Comments below.: References are sufficient and appropriate

3. Does the introduction state the objectives of the manuscript in terms that encourage the reader to read on? Please explain your answer under Public Comments below.: Could be improved

4. How would you rate the organization of the manuscript? Is it focused? Is the length appropriate for the topic? Please explain under Public Comments below.: Could be improved

5. Please rate the readability of the manuscript. Explain your rating under Public Comments below.: Difficult to read and understand

6. Should the supplemental material be included? (Click on the Supplementary Files icon to view files): Does not apply, no supplementary files included

7. If yes to 6, should it be accepted: After revisions.  Please include explanation under Public Comments below.

Please rate the manuscript. Explain your choice: Fair


# CCS 2021

## Review #72A


### # Overall merit
1. Weak reject

### Reviewer expertise
1. Expert

### Paper summary

Liveries supports time sharing a single SGX enclave across different (and
distrusting) short-lived tasks by restricting the untrusted code's access to a few key enclave security mechanisms such as attestation, and then sanitising
(recycling) it between uses. To enable this, the paper describes a call-gate-like mechanism whereby SGX instructions (ENCLU) are protected from arbitrary use by the untrusted code within the enclave, and demonstrates how to build nested attestation (in this thin trusted layer) on top of the base SGX primitives. A performance evaluation demonstrates low overhead for various machine learning algorithms.

### Strengths

 * Demonstrates how to create a more privileged layer of software inside
   a single enclave by restricting access to enclave management instructions
   (ENCLU) using call gates.

 * Presents a novel approach to multiplexing a single SGX enclave across
   different trusted parties by securely "recycling" it.

### Weaknesses

 * Limitations of the approach (e.g. use of multi-threading) make it impractical
   for many enclave applications.

 * The main justification for this system is that it avoids enclave creation
   costs, yet the cost of creating a large enclave from scratch was demonstrated
   to be *substantially* (orders of magnitude) lower using SGX2 instructions.
   Is any advantage left? We don't know, because the evaluation is only SGX1.

 * The analysis of side-channels is inadequate.

### Comments for author

Thank you for the submission. I found this an interesting read -- I'm very familiar with SGX, and I know that the lack of privilege separation inside enclaves has prevented many potential applications of enclave technology.
Sharing a single enclave across different trust domains using time partitioning is conceptually elegant and intellectually interesting.

Unfortunately however, it doesn't seem to be very practical. The limitations on multi-threading in particular are substantial, and seem likely to prevent (if not make life very difficult for) lots of potential applications. Given that, we have to ask: does the cost (such limitations) justify the benefit? Most of the evaluation shows that the technique has low runtime overhead, but Figure 7, which is inexplicably relegated to the appendix, shows why we might want to use
it: it is faster by one to two orders of magnitude to recycle an enclave than to create a new one from scratch (otherwise, we'd be better off doing that -- it has a smaller TCB, and fewer limitations). Great! But there's a glaring problem
here: in SGX2, it is not necessary to preallocate all the heap pages at enclave startup, and prior work (see the reference to Clemmys later in this review) has demonstrated that this *also* cuts enclave startup time by orders of magnitude.
Since the evaluation doesn't attempt this optimisation, we can't directly compare results, but it certainly makes me doubt whether this technique would ever be used in practice.

Besides these practical concerns, it's getting increasingly hard to ignore side-channels in papers using SGX. In this case, you have to deal with the fact that the attacker controls not just the OS (so they can single-step enclave execution, observe page accesses, etc.) but also vulnerable code *within* the enclave (everything outside an sblock). I'm far from an expert on side-channels, but it's not hard to imagine that this makes an attacker's job to extract crypto secrets being used by an sblock substantially easier.

## Detailed comments

 * Page 2:
   > The software TCB of the ESC and the SM has only 3200 lines of code. Using the modular software
   > verification toolchain SMACK [57], and the model checking tool Spin [36], we were able to
   > verify this TCB code in a day.

   Please state here briefly *what properties* were verified. Having read the paper, I think
   you verified basic memory safety and control flow properties, not anything like functional
   correctness.

 * Page 3:
   > In this paper, we assume that the service code itself is not malicious but potentially
   > vulnerable to exploitation, e.g., due to a memory-safety violation.

   This is unsatisfyingly vague -- what is the practical difference between malicious code and
   exploited buggy code? In the following paragraph, you say that the attacker has arbitrary
   read/write and control flow redirection primitives, so the reader is naturally left wondering
   what the attacker *cannot* do that they could if they could just write the service code? This
   shouldn't be a mystery. It's better to either state here that the attacker has full control over
   the service code (in which case, great!) or to give the reader some intuition on what the
   attacker cannot do in your threat model.

 * Page 4:
   > The key to limiting an enclave program's privilege is to restrict the use of security-critical
   > instructions. For example, EREPORT

   I think at this point you really need to stop talking about protecting access to EREPORT and
   EGETKEY and explain that the *instruction* you need to restrict access to is ENCLU. Actually,
   since ENCLU is only a 3-byte sequence (0F 01 D7), it's quite plausible that you could find those
   bytes in an executable page as part of some other instruction sequence (e.g. as an embedded
   immediate value inside a larger instruction). I'm very curious to see how this will be prevented.

 * Page 4:
   > To control those instructions, the ESC first finds them from all the code in the enclave
   > (service, SM and SGX SDK), and then builds a protective sblock for each of them. An sblock is a
   > set of instructions with an entry and an exit instruction, such that if the execution begins at
   > the entry instruction, it will leave the sblock from the exit instruction before running any
   > enclave instruction outside the sblock.

   This reads as if you look for ENCLU instructions (again, please be more precise about that)
   occurring in *source* code (or perhaps disassembly) of these software components, but since your
   attacker can arbitrarily redirect control flow you also have to worry about such instructions
   occurring elsewhere on an executable page.

 * Page 4:
   > Unaligned code gadgets that may reside within instructions or cross different instructions also
   > need to be found and removed

   Yes! This is much easier for WRGRBASE than ENCLU, however -- its encoding is longer.

 * Page 5:
   > Similar techniques for removing specific instruction gadgets have been used in prior research
   > [53, 64]: e.g., ERIM [64] performs binary rewriting to replace any sequence containing an
   > unaligned PKRU-updating instruction with a functionally equivalent sequence without the
   > instruction

   ERIM is a great example -- the paper includes an analysis of the frequency with which the
   problematic byte sequences occur in other executable code, and a strategy for rewriting such code
   to benign equivalent sequences. I'm missing that level of analysis here, although the ERIM
   rewrite strategies seem like they would be applicable.

 * Page 5:
   > ESC disables multithreading in enclave (see 𝑃1 in Sec. 4.1) and enforces an exception policy
   > (𝑃2) to ensure that the thread can only reenter the enclave through ERESUME, so the execution
   > will resume from where the interrupt happens with all enclave state intact. Under these
   > security policies, we can protect security-critical instructions using sblocks.

   I agree, but it might be helpful here to mention explicitly that the reason you don't have to
   worry about the attacker redirecting control flow by writing to the SSA is exactly because the
   enclave is single-threaded, so they cannot mutate it during an exception.

 * Page 5:
   > Access to the register is restricted by the compiler and further checked to ensure that no
   > gadget in the enclave can be leveraged to violate the policy through binary code inspection.

   What do you do if you find a possible gadget for WRGSBASE? Just fail compilation?? In reality
   this check would need to happen during or after final linking, when relocation offsets are known.

 * Page 6:
   > As mentioned earlier, Liveries protects critical instructions like EGETKEY and EREPORT using
   > sblock chains. On the binary code level, however, these instructions are all compiled into
   > ENCLU, which invokes different SGX non-privilege leaf functions (EGETKEY, EREPORT, etc.) based
   > upon the parameters set in the register EAX [11].

   Thank you! I think if you had briefly acknowledged this in the preceding sections I would have
   been fine waiting until now to know how it was handled.

 * Page 6:
   The sample code in figure 3 has a couple of bugs:
    * It sets the full 64-bit GS base, but compares only the low 32-bits (this is odd, yet looks benign)
    * It corrupts the result register of EACCEPT (RAX is stomped by 0xdeadbeaf).

 * Page 7:
   > Specifically, the SM sets a marker in the SSA for the thread, e.g., writing 0 to the address
   > within SSA that reserved to store rip. The value will be overwritten if an exception happens.
   > If an exception is detected, the SM performs exception management according to 𝑃2.

   This sounds strange. If the enclave takes an exception because of a jmp/call to 0 (e.g. a NULL
   function pointer), then SSA.RIP will be 0. Why don't you use the exception info field of the SSA
   frame, or even just look at whether this is a nested EENTER, provided in EAX at the entry point?

 * Page 8:
   > SGX2 has introduced a new set of leaf functions with the following capabilities: (1) dynamic
   > creation and addition of a page to an already initialized enclave; (2) update of an EPC page's
   > permissions; (3) change of an EPC page's type. These operations once invoked through supervisor
   > leaf functions (e.g., in the case of changing page type to TCS) will take effect only when
   > their results are accepted by the enclave code using EACCEPT

   This is not correct. EMODPE (which increases page permissions, e.g. making an executable page
   also writable) does not require EACCEPT.

 * Page 8: If you are going to host non-trivial (e.g. C library code) in sblocks, you need to do
   more than just ensrue that the block executes atomically, but you also need to prevent the
   attacker from calling it in an unexpected state that doesn't trigger an exception yet still
   alters its behaviour. One that comes to mind is ABI poisoning (see Alder et al, ACSAC'20). To
   defeat such attacks I think you probably also need to sanitise the flags register and
   FPU/extended state on entry to an sblock.

 * Page 8:
   > checking the nonexistence of ENCLU and WRGSBASE gadgets and then granting the pages with read
   > and execute permissions (which cannot be later altered by unauthorized enclave code since
   > EACCEPT is protected)

   This can't work as written, because EMODPE does not require EACCEPT. I suspect you can put EMODPE
   in an sblock and protect it in the same way, but as described the scheme is broken.

 * Page 8:
   > when the enclave is about to handle secret data (e.g., decryption of users' session keys using
   > keys derived by EGETKEY), our design guarantees that the enclave has only 1 TCS page and is
   > thus single-threaded. After all data for the user's task batch is prepared and all secret data
   > is cleared, we add more TCS pages back to the enclave

   Adding/removing TCS pages must make this incredibly slow. It's also hard to implement correctly
   -- you need to synchronise with those threads, save/restore their context, etc.

 * Page 9:
   > GS should be restored from the TCS on EENTER and ERESUME. Indeed this is the case according to
   > the official manual [11, Volume 3, 40.4], which states "(on ERESUME,) new values (of FS and GS)
   > are constructed using TCS.OFSBASE/GSBASE (32 and 64-bit mode)"

   This is a minor bug in the spec's description of the instruction. However, if you look at the
   instruction pseudocode for ERESUME (at least the latest version) it is correct: FS and GS bases
   are restored from the TCS only in 32-bit mode; in 64-bit mode they come from the SSA. That is in
   fact is necessary for your atomic blocks to function correctly even on SGX1, because otherwise an
   AEX during an atomic block would clear GS base.

 * Page 9:
   > Since the development and deployment of SGX2 are still in the early stage

   Hardly. SGX2 shipped in Gemini Lake NUCs like yours in 2017 and Ice Lake clients in 2019.

 * Page 9:
   > We confirmed that the enclave crashes if the TCS page being removed is in use by another
   > thread.

   This does not inspire confidence. How do you know that those "crashes" are not a source of
   potential vulnerabilities?

 * Page 9:
   > The last step is to remove the (unaligned) occurrences of ENCLU

   What do you mean by "(unaligned)" here? I think you mean that they are embedded in the
   instruction stream but are not on expected instruction boundaries. This isn't the same thing as
   alignment.

 * Page 10:
   > We further performed a functional verification on the sblocks using model checking (Spin [36]),
   > which proves that the model derived from each sblock has desired properties.

   Model checking is not the same thing as verification, unless it is exhaustive. Your example model
   is simple enough that I assume you did indeed do exhaustive model checking, but It would help to
   make that clear.

 * Page 11:
   > The remote attestation needs to connect to the Intel attestation server and may take seconds.

   This is true only for the original (EPID) SGX attestation, not the newer DCAP scheme. The system's
   certificate chain can be cached avoiding any extra round trips in the general case.

 * Page 11:
   > Figure 7 (Appendix A) shows the comparison of the delay for creating and destroying the enclave
   > with that for integrity check and exit sanitization (averaged over 100 measurements). Even
   > without taking the time for remote attestation into account, our approach is still orders of
   > magnitudes faster: e.g., when the heap size is 1 MB, our approach is 827× faster.

   The text here doesn't describe how you are creating the enclave, but if I had to guess this is
   SGX1, and each heap page is being added (EADD and EEXTEND) statically at enclave creation time.
   This can be made *much* faster using SGX2 instructions and adding the pages after enclave
   creation. See for example Table 1 of the Clemmys paper (Trach et al, SYSTOR'19) which reports
   SGX2 startup times for large heaps as a fraction of what they were on SGX1. I wonder whether in a
   true comparison of a realistic enclave using SGX2, the remaining performance benefit (if any)
   of your enclave recycling approach would not justify the significant downsides.

   Also: it's inappropriate to refer to a figure in the appendix when it is essential to
   understanding the body of the paper -- this is space cheating.

 * Page 12:
   > only 1 gadget in concern appears across the instruction boundary across all binaries

   Although I agree with your ultimate conclusion that rewriting is practical and cheap, I'm not
   sure how you can make this statement in a general sense. Since ENCLU is a 3-byte sequence, it can
   appear in any instruction that embeds a 32-bit immediate, such as a CALL or LEA which are very
   common. The value of the immediate depends on how the linker lays out the final enclave binary,
   i.e. it is highly unstable, and looking at existing binaries (especially if they are just
   libraries) is not terribly meaningful.


#### Nits

 * Page 2: "rollbacked" -- rolled back

 * Page 3: "Asynchronous Exit handler Pointer" -- asynchronous exit point

 * Page 4: "delay for each request1." -- \footnote goes after the punctuation (.)

 * Page 5:
   > The enclave is configured to disable multi-threading by setting TCSNUM to 1

   I am not sure what TCSNUM is. I can obviously guess, but this would be clearer as "by creating
   only a single TCS"

 * Page 5: "which uses of a"

 * Page 8: "an thread"

 * Page 9: "Ivybridge" -- Ivy Bridge

 * Page 12: "gadgets in popular enclave binary" -- binaries

### Questions for authors’ response

If I'm targeting SGXv2, and I use the obvious optimisations of adding heap pages dynamically on first use rather than measuring them statically at enclave creation time, what performance benefit remains to recycling the enclave rather than creating a new one? (I realise that you can't answer this question directly without new experiments, which is not allowed, but I'd appreciate some insight into the scenarios where you still expect this technique to retain value.)

### Concerns to be addressed during the revision/shepherding

 * Fix bugs in assembly code (Figure 3).
 * Describe mitigations to ABI poisoning attacks.
 * Improve incorrect description of SGXv2 features (restricting use of EMODPE).

## Review #72B

### Overall merit

1. Weak Accept

### Reviewer expertise

1. Knowledgeable

### Paper summary

The paper presents Liveries -- an approach to allow sequential processing of tasks from different users in SGX enclaves bypassing the need for complete re-initializing of the enclave between tasks. The initialization steps in SGX is an expensive process; performing this initialization when running a large number of small tasks introduces very large overheads. Instead Liveries seeks to allow each task to leave some persistent data behind after execution that cannot be accessed by the next running task. Liveries does this by

(1) imposing restrictions on executing code to ensure that each task cannot leverage privileged instructions to access other user's data

(2) ensuring that a task does not leave behind user input or temporary data in memory which the next task can access

These restrictions in turn are powered by three key insights

(1) Running of privileged instructions such as those to retrieve keys, only inside of sblocks -- code blocks which have a known entry and exit instruction.
These sblocks use the (typically unused) register, gs, as a dedicated register to store flags to at the beginning of the code, which are checked at the end of the code, preventing use of ROP gadgets in the security monitor. This is combined with binary rewriting to eliminate code gadgets that inadvertently produce the bytes for privileged instructions or use of the gs register.

(2) Providing a runtime that configures enclave setup and mediates any interactions may modify the configurations of the enclave. The runtime is also responsible for tasks such as providing memory spaces (for temporary data, user input data, and measured fixed input data), as well as clearing, checking, or restoring memory spaces as appropriate between tasks. The use of this runtime is demonstrated through evaluations where the code of several machine learning tasks are modified to use this runtime.

(3) Correct design and handling of signals, exceptions and interrupts to ensure these do not break the abstractions introduced for security.

Additional important contributions are the design for safe use of multi-threading in SGX2 with Liveries and verified implementations and models of runtimes.

### Strengths

- Clear explanations of a relatively novel use case with compelling performance numbers

- Clever and simple design of the ESC through sblock chains that provides simple important security invariants.

- Implementations that are verified using model checking and other approaches.

### Weaknesses

- Analysis of related work and the positioning of Liveries against alternate designs is incorrect and limited.

- Some of the writing makes it hard to follow the design in places and some of the claims are too broad (more details below)

### Comments for author

This was an interesting paper and design. I think the presented design has many strengths which are compelling, in particular the relatively compact and elegant design. For the rest, of this summary, I will thus focus this discussion on a couple of important aspects that should be addressed before publishing.

1) Comparison with SFI and related work -- I was surprised to see this already raised in the prior reviews.  I actually believe when comparing Liveries to SFI, this paper includes claims about SFI that are simply not true and must be corrected for a more accurate comparison. To be clear, I believe Liveries offers a compelling alternative design point, but this should be demonstrated by comparing accurately against related work. Here are some specific details

- "SFI ... requires heavy code analysis to find all valid control flow destinations" -- This is not true for most SFI schemes and as written applies to CFI (control flow integrity schemes). SFI schemes like Native Client do not have such requirements, while SFI schemes such as WebAssembly simply use tables as an intermediate step for indirect function calls -- a process that explicitly does not require "heavy analysis"

- "SFI requires ... large TCB for verifying SFI compliance, including the disassembler and binary analyzer (about 100K LoCs)". While I am not familiar with this work, as it looks quite new and is yet to appear, the state of the art techniques for verifying SFI compliance do not require a 100k LoC disassembler or binary analyzer.
[Rocksalt](https://6826.csail.mit.edu/2017/papers/rocksalt.pdf) builds a verifier for Native client in 80 lines of C code (See [here](https://www.seas.harvard.edu/news/2012/07/nacl-give-way-rocksalt)).
Perhaps the SFI verifier compliance used in this domain requires additional verification that actually results in a 100k LoC verifier, but in this case, you need to clarify why a standard SFI verifier approach such as Rocksalt is not the correct comparison point.

- Nit- "SFI is designed to sandbox concurrent tasks within an enclave" ==> "SFI can be used to ..."

Optional suggestions on comparing to SFI:

- An interesting point, you could choose to highlight, is that the use of transaction blocks (called sblocks here) and approaches to prevent stack vulnerabilities (in this paper, the verification does this) are techniques commonly used in SFI schemes. [Native
Client](https://research.google/pubs/pub34913.pdf) uses bundles (which you can think of as fixed size sblocks) along with control flow restrictions to ensure security checks cannot be bypassed. WebAssembly uses
[SafeStack](https://www.usenix.org/system/files/conference/osdi14/osdi14-paper-kuznetsov.pdf)
to prevent stack vulnerabilities from affecting guarantees.

- I also think there are other considerations which make your approach more compelling than SFI for this problem space including the maintenance burden of maintaining an SFI compiler toolchain, runtime and verifier, etc.

2) Presentation of Liveries -- there are several parts of the paper that I found hard to follow, which makes it challenging to assess the security of the overall design.

- I found it difficult to understand if the security checks in sblocks have to be tailored to the privileged instruction being protected. I think the answer is yes; however, I had a hard time finding a full list of all the privileged instructions being supported and the specific security checks or steps taken in the sblocks to secure each one. The current explanations are a bit scattered through the paper, which makes it challenging for me to get a global view of the security of the system. (For instance, I see some text in P3 in section 4.3, some text in Figure 4 etc.) A table here focussed on the security checks imposed would go a long way.

- A couple of times you mention function pointers in the paper text, without really explaining what these function pointers are, and why they matter. Please clarify this.

- The details in Section 6.2 need to be summarized or at least forward referenced much earlier. Much of the paper left me wondering precisely how one identifies/who identifies the secret data or whether all memory being operated on was considered a secret / needed to be checked for integrity etc.

### Questions for authors’ response

Apart from any clarifications you can provide to my request for changes in the summary, I also had a couple of minor questions

- Section 5 indicates, for dynamic loading of code, you first load the code with the page on read+write permissions, perform the binary gadget check, and then change to read+execute. Is there a possibility of a parallel thread that changes the loaded code between the check (which is performed on a read-write page) and grant of execution permissions (which removes the write privilege)?

- Reference to time sharing vs sequential scheduling in the abstract (I suspect this was a missed edit from your last draft. I am not sure the system as designed can be called a time-sharing system)


## Review #72C

### Overall merit

1. Weak reject

### Reviewer expertise

3. Knowledgeable

### Paper summary

TEE security is based on the idea of an inductive security proof, where a TEE's initial state is strongly attested and so the user can guarantee that it must be in a state that is reachable from the initial state.  The paper asserts that startup costs are high for enclaves and therefore proposes a mechanism for resetting an enclave to its initial state.

### Strengths

### The paper presents a nontrivial engineering effort to implement techniques that allow an SGX enclave to be reset after creation.

### Weaknesses

The introduction repeatedly asserts that attestation requires communicating with the CPU vendor.  This has not been the case for SGX for a while and is not the case for other system.  Modern attestation flows bake the attestation quote into a certificate that is signed by the root of trust or quoting enclave.  The client needs only to check that the signing certificate has not been revoked, which can be done with a cached CRL or similar.

My biggest problem with this paper is that it is *very* easy to build snapshot and restore functionality into a TEE design if you start with this as a goal.  This is rarely done, because it is hard to avoid replay attacks.  Identity binding is one of the hardest problems with TEEs: it is hard to differentiate between a pristine enclave that is ready to load some data and an enclave that started in that state and has now been moved to a specific later state.  The Intel SGX2 ConfigID register was added explicitly to address this.  The design of this work is to build a replay attack into the TCB and then try to secure the mechanism such that it will only replay from specific points.  The security evaluation looks solid but I may have missed something.  Building this functionality into something like SGX from the start would be trivial (SGX1 maintains a Merkel tree over the whole of enclave memory so a lightweight snapshotting mechanism would have a very lightweight lazy validation path using the existing hardware / microcode).

Both the problems that are being addressed (enclave startup time is high) and the solutions are very specific to a single TEE technology.  The problem is not intrinsic to TEEs (the limit on TEE creation is the ability to compute a signature over the initial memory image, symmetric crypto can run at memory-speed and the asymmetric part runs only over the hash of the remainder and so the upper bound on performance here is a few cycles off the performance of an approach that requires memory resetting).  The solution is closely coupled with the SGX abstractions (for example, a single privilege domain within the enclave).  The same abstraction on Intel TDX or AMD SEV-SNP, for example, would boot a small OS image and create a zygote process, then create CoW copies of it for each request.  

The techniques used here appear to be minor tweaks to those in *Nested Kernel: An Operating System Architecture for Intra-Kernel Privilege Separation* (ASPLOS '15), with a slightly different use case.

### Comments for author

The fact that your approach basically boils down to a replay attack on the attestation mechanism makes me incredibly nervous.  I think it is fine within your constraints but there are a lot of subtle interactions between parts of the security model that all have to be right for this to work.

### Comments

## Rebuttal Response by Wenhao Wang <wangwenhao@iie.ac.cn>

Thank you for the comments.

* To Review A and C (motivations, enclave creation/attestation flow):

Besides heap allocation, an enclave may take time to initialize its hosting service. Considering KANN as an example, building the neural network data structure and loading parameters (with preallocated heap) take over 200 ms for a CNN model with 40 MB weights. Liveries avoids the overhead by resetting the enclave to the trusted state after the initialization (taking less than 10 ms). We can conduct more experiments to evaluate the service initialization time for other use cases.

Also importantly, Liveries provides additional protection even when the time of enclave creation, attestation, and termination can be afforded for each user request. In the absence of the protection, the adversary can control the enclave through a malicious request that exploits vulnerable enclave code. As a result, he will be able to forge a “legal” enclave report for a malicious program outside the enclave (i.e., the man-in-the-middle attacks against remote attestation [19,48]). While the threat might be mitigated using a different enclave image for each user (so that the enclaves’ measurements would be different), it introduces the burden that the service providers may be reluctant to bear. 

* To Review A (side channels):

Liveries is meant to protect a user’s data from a malicious user of the same in-enclave service. It does not introduce *additional* side channels except in-enclave transient execution attacks. This threat can be mitigated by inserting serializing instructions after critical instructions, which prevents out-of-order execution (Section 8). We can provide a more thorough analysis in a new version.

* To Review A (SGX2):

We designed Liveries to support multi-threading on SGX2 (Sec. 5). We’ll discuss the hardware changes needed for secure multi-threading, e.g., GS could be stored into SECS on AEX and restored from SECS on ERESUME.

* To Review B (SFI):

We agree heavyweight code analysis may not be needed for SFI. Rocksalt is designed to support only a small subset of x86 instructions, and it assumes NaCl uses segment registers to enforce most of the SFI policy, which are not available in x64 enclave code. 

* To Review B (dynamic code loading):

To prevent TOCTTOU attack, dynamic code loading is allowed only when the enclave is single-threaded (by dynamically adjusting the number of TCS pages).

* To Review C (replay attack):

We appreciate the reviewer’s insightful comments on enclave snapshot and restoration. Liveries is carefully designed to secure such a mechanism so it will only replay from specific points, in which the previous user’s state is sanitized to prevent information leakage and the interactions with follow-up computations (Sec. 4).

We are willing to provide more information to address the reviewers’  concerns about the current design of Liveries, such as ABI poisoning attacks, which can be mitigated through sanitizing processor extended state on enclave entry. Also, we will revise the paper according to other review comments, including fixing bugs in assembly code, correcting the description of SGXv2 (EMODPE), clarifying exhaustive model checking, comparison with _nested kernel_, and improving the presentation.

### Comment @A1 by Reviewer A

Dear authors, thank you for the rebuttal. The reviewers considered it, but we remain concerned that the added complexity and security risks of the proposed approach outweigh its performance advantages over creating a fresh enclave. In a future revision, you may wish to consider performing an evaluation against SGX2 enclave creation (with lazy heap/stack allocation).





# Okland 21

## Review #85A


### Overall merit

1. Weak reject - The paper has flaws, but I will not argue against it.

Reviewer expertise

3. Knowledgeable - I know the area well (key related work is quite familiar
   to me).

### Reviewer confidence

3. High

### Paper summary

This paper presents Liveries, a system for securely multiplexing SGX enclave instances. This is important because a large class of applications use a client server model where the costs of bringing up and tearing down an enclave per request would be costly. Instead, this research proposes to multiplex the single SGX server environment for many different clients while ensuring that the secrets and measurement values for attestation are safe from corruption. A prototype is built that explores efficacy on machine learning problems.

### Strengths

+ Use of GS/FS as a flag register for 1) forcing entry to sensitive code 
+ blocks
at the beginning---getting complete mediation---and 2) protecting exit---ensuring atomicity of the code block and return state.

+ Tackling the problem of creation and tear down of SGX enclaves for 
+ client
server architectures

+ Formally describing and verifying the sblock atomicity property

+ Prototype and evaluation with real applications

### Weaknesses

- Poor description of the time sharing model, which appears to be a batch model
  instead

- Lack of details on where data is located and how loading and isolation work

- Lack of experimentation on systems issues: concurrency and context switching

### Detailed comments for authors

Overall, I am quite interested in this novel idea of multiplexing a single SGX enclave across multiple separate principles. I think the programming model has not been explored and this presents a new direction and valuable system towards that end. I also appreciate the application of single privilege level virtualization for SGX. While this technique in general is not new (Bare Metal, ERIM, PerspicuOS, etc.) this is the first application to SGX enclave environments. In particular, the unexpected technique was to use the GS/FS flag to ensure entry and exit gate atomic properties. I also appreciate the implementation. 

Unfortunately, the paper claims a timesharing model for SGX, but never presents a system with abstractions for general use. It isn't clear to me whether this is just simple batch processing or if it truly is some more general form of timesharing. If the paper were to narrow its claims and present an execution environment that is placed within SGX by isolating critical state, and describe more clearly transitions between clients within the enclave, I could see this being a fantastic paper. As it is, I don't understand the fundamental design elements and am even concerned that they really aren't timesharing in the traditional sense. A few more detailed comments follow.

**Analysis of Problem and Motivation**:

The main problem presented is the expensive cost to bring up and teardown an SGX enclave and how the costs do not fit well with client-server architectures, specifically machine learning programs. The authors propose multiplexing an enclave instance across many clients. I believe this is a great and real problem and am interested in seeing it solved. 

**Analysis of Claims**:

The primary claims of the work are: 

1. Lightweight user isolation: This paper does present an intra-enclave privilege separation implementation.

2. Verifiable protection: the authors do formally specify and verify a subset of the control-flow properties related to the sblock abstraction

3. Implementation and Evaluation: the authors do implement the system described and evaluate it, however, the evaluation leaves many open questions as described below.

**Analysis of Approach**:

In general, the design is unclear to me. From the description provided I would see this as a nested security monitor within an SGX enclave (like Hodor or ERIM), but the claims of the paper present a timesharing multiplexing scenario.
A few key issues:

- This is not multi-threading or time-sharing. Ultimately, it appears to be
  about leaving a few pieces of state active in an enclave to avoid redoing
  measurements, and then making sure that the small amount of state isn't
  touched by a compromised enclave while it is running on something else.

- There is no protection model or definition of a principle or objects or
  context switching. I believe this work overreaches in its claims. It does
  provide a powerful protection model for a small set of data which can allow a
  batch model to avoid certain loading/cleaning steps to make enclave use much
  more efficient. In some sense it seems to enable enclave reuse by caching
  certain data (measurements and client workload) and protecting the cache from
  corruption.

- The basic ideas of isolating different client data makes sense,
  encrypt/decrypt, but the process for interleaving execution was not clear.
  This could heavily influence performance costs. An additional factor that
  wasn't clear clear was how the size of the data influenced performance. If
  the size of the memory to be saved increases then the relative costs of
  attestation would be less. Another key element missing is what happens at
  scale? 1,2,4,8, etc. different client's all interleaving requests. In
  general, these are all systems design and experimental issues that I would
  expect from a paper multiplexing and claiming efficiency over a baseline.

**Nits**:

- What is a `leaf` instruction?

### Requested changes

- Change the claims about timesharing or validate them with a clear design and
  evaluation
- Provide a more clear description of how state is loaded and stored as the
  number of clients and data amount increases
- Evaluate points mentioned in the third bullet above: frequent interleavings,
  interrupts, etc.; differing sizes of data; scaling concurrent clients in the
  same enclave at a time


* * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * * *


## Review #85B


### Overall merit

3. Weak accept - While flawed, the paper has merit and we should consider
   accepting it.

### Reviewer expertise

3. Knowledgeable - I know the area well (key related work is quite familiar
   to me).

### Reviewer confidence

3. High

### Paper summary

The paper proposes a mechanism to share an SGX enclave and its attestation between successive users, e.g. successive remote clients of a secure service. This relies on a small bootloader, a security monitor, and a security invariant that prevents the rest of the code loaded into the enclave from accessing the SGX primitive capabilities such as sealing and attestation. Conversely, code with these privileges is carefully reviewed and protected to ensure it runs without interference from the rest of the enclave (or causes the enclave to fail safely). The approach yields useful security guarantees with a simple TCB and a low overhead.

### Strengths
----
- The TCB is small and simple.
- The proposal is well presented, analyzed, implemented, and evaluated.
- The sblock abstraction and its implementation are of independent interest.

### Weaknesses

- The paper leaves side channels for future work. This is a big limitation for any SGX-related paper. More specifically, side channels between users within the same enclave are clearly not something Intel would even try to mitigate. 
- The paper does not consider concurrency (except for a brief extension outline), important for many client-server applications that would benefit from its approach.
- The formal development is disappointing. Section III and its theorem are particularly informal. The use of model-checking is interesting but poorly explained. More generally, it seems hard to verify meaningful security property without a detailed (partial) model of SGX and its instruction set.

### Detailed comments for authors

The claim that SGX is "not designed to support sharing of an enclave across different users" is misleading. This is actually fully supported, based on each user verifying remote attestation materials and reviewing the corresponding code. More specifically, this paper's proposal provides some protection against exploits in that code, but still relies on its shared understanding and careful review by all users that need to trust the enclave. 

In III-E, the comparison with SFI and similar approaches is unnecessarily harsh. Those approaches also provide application-level guarantees not covered here. For instance, memory safety bugs in the enclaved code can still be exploited, even if it does not gain access to the protected SGX instructions.

Regarding sblocks, can would provide additional details about the stack? Should we be concerned about register spilling, or stack overflows? 

IV-A Who initially sets OGSBASGX in the TCS? Is is attested? 

Related work: see "A Design and Verification Methodology for Secure Isolated Regions" by Seshia et al at PLDI 2016.

There are also many papers that similarly filter out specific instructions out of binaries before making them executable, with minimal overhead and rewriting.

### Requested changes

- some discussion of side channels
- a more complete and balanced discussion of related work
- a clearer discussion of what is actually formally verified, and against what architecture model An implementation with support for concurrency and dynamic loading would also help.


## Review #85C


### Overall merit

2. Weak reject - The paper has flaws, but I will not argue against it.

### Reviewer expertise

4. Expert - Historically an area of primary focus, or an area I have done
   recent, significant work in.

### Reviewer confidence

3. High

### Paper summary

The paper proposes a method for adding isolation within an SGX enclave. The isolation is sequential. That is, user B can use the same physical enclave as user A after user A is done using it.

### Strengths

- Liveries is based on a very detailed analysis of low-level processor properties (including but not limited to SGX). 
- Liveries is formally verified.

### Weaknesses

- The threat model seems inconsistent with the informal security goals.
- The motivation of the work is somewhat unclear.
- Liveries has to impose various restrictions on the enclave code that limit its usability.

### Detailed comments for authors

Isolation within an SGX enclave has been an elusive problem. The paper presents a method that achieves at least a limited form of isolation (i.e., sequential). In spite of the limitations, this is tricky work, and the authors appear to have done a thorough job going through the low-level attacks and eliminating them. The formal verification of aspects of the system is also positive.

Suggestion 1: Clarify the motivation of the work. It seems plausible that Intel intentionally avoided the complexities of an in-enclave isolation mechanism because (a) complexity is bad and (b) users can just create another enclave. The paper states that creating another enclave is too slow. Really? This can only be the case for enclave jobs that are so short (e.g., <1 second) that the enclave setup time dominates the useful lifetime of the enclave. If the computation time for the job is so short, why does the user need to run it remotely in the cloud or some other shared environment and inside an enclave? The user's laptop or even his phone should have adequate resources for this type of job and avoid mountains of security problems and complex fixes.

Suggestion 2: Clarify the threat model: Liveries focuses on a few crypto keys. The paper calls these the user's critical data. However, session keys are a secondary concern. The user's really critical data are the data that the service running inside the enclave needs to operate on (e.g., inputs to the ML code). The paper's threat model allows the adversary to perform "arbitrary memory reads and writes." Given this, why can the adversary not just copy all the user's data out of the enclave?

Suggestion 3: Clarify multithreading: Of the various restrictions Liveries imposes, requiring the enclave to be single threaded seems to be the most severe. The performance implications are obvious. The paper attempts to remove the restriction in the discussion. However, the discussion is too short to be convincing. In particular, why can't the adversary with arbitrary memory read and write capability just read all user data out of the second enclave?

**Other observations**:

The paper describes the problem in terms of TEEs. However, it is quite clear that the hardware model as well as the paper's solution are specific to SGX. For example, the TEE situation described in the paper does not appear to apply to TrustZone.

Theorem 1 covers only an abstract representation of sblocks, but not the actual SGX implementation.

Given the threat model (attacker has arbitrary read and write and can change control flow), the SM seems purely heuristic. That is, all the attempts by the SM of preserving confidentiality and integrity are a lost cause in an threat model in which the attacker can read/write anything at any time.

The experiment in Figure 8 does not reflect a real workload.

Gadget elimination appears to require source code.

# Usenix 20

## Review #670A

### Review recommendation

2. Reject and resubmit

### Writing quality

2. Needs improvement

### Reviewer interest

2. I might go to a talk about this

### Reviewer expertise

2. Some familiarity

### Paper summary

This paper makes applications (from various sources?) share a service that runs in an Intel SGX enclave. 
Basically, it creates an enclave for a library-like function, called the service, and lets applications use it in a shared manner. 
In addition, it fights against potential memory corruption attacks from the applications using the service. 
Specifically, it prevents the attackers from expoliting the secrets of the service, or secrets of other applications using that service. 

This work, first, brings back the problems that isolation execution (e.g. Intel SGX) fights against, because it proposes the shared use of enclaves. 
Afterwards, it protects applications from these problems with CFI-like solutions. 
In summary, this is too much of a CFI solution specific for SGX enclaves. 
For example, it aims at preventing the use of SGX specific critial instructions with attacker chosen arguments. 
Besides, it also employs conventional protection mechanisms against code-injection attacks, such as W-xor-X.

### Strengths

+ Introduces a new use model for the Intel SGX. In comparison to protecting a part of an application, it protects library-like functions used by various applications in a shared manner. 

+ Performance evaluation is made not only on a benchmark suite, but also on machine learning applications for which Intel SGX is an interesting target.

+ It is kind of a CFI solution, employed for an Intel SGX enclave, preventing malicious code executing SGX specific critical instructions without authorisation. Constraining the CFI to SGX gives advantages to the design.

+ No hardware extension is required. The software trusted code base is small. In addition, verification is made possible to check if the proposed code compilation technique is applied properly on the trusted code base.

### Weaknesses

+ Isolated execution environments such as Intel SGX or PMAs (Protected Module Architectures) aim at preventing shared use for security. However, this paper proposes the shared use of isolated execution. Therefore, its basic idea is a bit odd.

+ Section 2.4 describes the thread model. According to the model, the adversary knows the service code, can perform arbitrary memory reads/writes, and can manipulate the service???s control flow. Basically, the attacker's capability is  to exploit memory safety problems (such as buffer-overflow vulnerabilities). This is too much like the attacker model for any critical software, against which isolated execution is introduced. Hence, this work brings back the problems first with shared enclaves, then fight against them with CFI-like solutions.

+ "Runtime Integrity Check" feature of the described "Security Monitor" is not run-time. It performs checks before and after execution. The name seems poorly picked.

+ A PKI scheme is described for the uploading data to services at runtime. However, it is poorly described, i.e. a trust-model is not given. It basically requests user-data to be signed by the service provider's private key. How will this happen? Can use data be given the service providers without trust issues? Will the service providers be available to sign the data at any time?

+ There are other issues regarding the use of cryptography. For example, the authors say that they use ECDH, but they don't refer the curve? Does it have a secure curve, a fast implementation, or a small code base? How these affect the design?

+ Section 3.2 was very hard to understand. It encapsulates a critical instruction I, with a code triplet: C, entry, and exit. The description of C is still unclear to me. Is it a compiler generated code? If yes, how the compiler does it? Is the exit (which is also the entry of next block) also the critical instruction, I? What happens if the code before or after the I, does not form an sblock by the given definition?

+ The flow of the text is in general very tiring, although the language use is good. For example, the Section 3.2 mentions that, there is an integrity check for "critial system parameters". What are these critical parameters? It is not described. Several paragraphs later, an example is given for a biomedical service, and only then it becomes clear.

+ The results are interesting but not explained. Reserving a CPU register (making the benchmark code run without using that register) does not affect the performance badly, and sometimes even improve it. Unfortunately, a discussion is not provided for a potential reason. Hence, it shall make the readers question the quality of the performed experiments.

+ The abstract should have mentioned that, this work is specifically designed for Intel SGX. Also the authors could provide a discussion about the other architectures, such as Keystone enclaves, or Sancus protected modules.

### Detailed comments for authors

+ Page 2: Using the term "Verificable protection" at the introduction is very vague, because it does not mentioning what it verifies. What kind of verification is it? Formal verification? Memory-vulnerabilities? Correct implementation of the proposed code block-chain? These questions are only answered later at page 10.

+ Page 4: What is VK?

+ Page 6: The following sentence is not clear: Since exit_j=1 is also entry_j+1 , so exit_j+1 is also reached, until exit_n+1 is run and flag is verified and reset?

### Requested changes

+ The authors should motivate the reason why the enclaves are shared, in contrast to using them for isolated execution that they are designed for. Especially, it should provide a distinction between the security problems that enclaves fight for with isolated execution, and the problems introduced with their shared use.

+ The authors might not have experience on designing a PKI system, and chosing the right crypto algorithms. So corresponding sections need improvements.

+ A discussion is required for the effects of reserving one CPU register over performance, especially why it yields a speed up. Not having such a discussion will make the readers skeptical about the quality of the performed evaluation, and make them question if the authors know what they are doing.

+ Language use is quite good, but improvements can be made over the structure. The authors should not refer to a term, that will be explained several paragraphs or sections later. If they make such references, they should at least provide a hint, that the term will be explained later.


## Review #670B

### Review recommendation

1. Major revision

### Writing quality

1. Well-written

### Reviewer interest

1. I might go to a talk about this

### Reviewer expertise

1. Knowledgeable

### Paper summary

This paper deals with trusted execution environments (TEEs). More specifically, the authors focus on a particular TEE, i.e., Intel SGX, and consider the problem of having enclaves _shared_ among different users -- that is, the enclave code processing data from multiple, potentially distrusted, users.

To tackle this problem, the authors propose a new security architecture, dubbed Liveries, which allows sharing the enclave code and processing data from multiple users, on par with the security guarantees of SGX. Liveries builds upon three main components: (1) an enclave security configurator (ESC), (2) a security monitor (SM), and (3) a control-flow enforcement scheme.

ESC is responsible for initializing the enclave and setting the run-time environment in a way that guarantees the following properties:
- P0: W^X memory protection policy on enclave pages -- code is mapped as RX,
  while data are mapped as R/RW. More importantly, in SGX1, page table
  permissions are part of the enclave measurement, and so by setting them
  accordingly in the beginning, ESC guarantees "lifetime" P0.
- P1: Single-threaded enclave: multiple, concurrent execution threads are
  effectively disabled by configuring the enclave accordingly (set `TCSNUM = 1`).
- P2: Secure exception handling: multiple exception threads are also disabled,
  again by configuring the enclave accordingly (set `NSSA = 1`). In addition,
  the entry point to the enclave is set to the run-time SM, which, in turn,
  checks if the invocation was via `EENTER` or `ERESUME`. In the former case, it
  transfers control to the enclave's true entry point, _iff_ a critical basic
  block of execution (_sblock_) was not interrupted (more about sblocks later);
  in the case of `ERESUME` the interrupted execution thread continues as usual,
  as `NSSA = 1` guarantees non-tampered continuation.
- P3: Protection of critical instructions: the execution of critical
  instructions, such as `EGETKEY` and `EREPORT` are protected by the sblocks
  scheme (again, more about sblocks later).
- P4: Protection of critical data: per-user data are protected via encryption.
- P5: Non-bypassable SM: the data of the run-time SM are sealed and the
  (immutable) entry point of the enclave is set to the SM (see P2 as well).

SM is basically "injected" inside the enclave and guarantees the integrity and secrecy of the per-user data (again by using SGX primitives). The high-level idea (apart from aiding with the enforcement of P2) is to manage three different memory areas (per-user, inside the enclave): `MEASURE_AREA`, `TMP_AREA`, and `ENC_AREA`. `ENC_AREA` is used for holding user-critical, persistent information, such as session keys, _etc._ `TMP_AREA` is used for storing (temporal) user data, while `MEASURE_AREA` is used for keeping data that are used for attestation. SM also makes sure that all areas apart `ENC_AREA` are zapped (along with SSA and certain CPU registers), when it switches to process a request/task of a different user. Lastly, SM is also made _atomic_ via sblocks.

_sblocks_ are essentially a control-flow enforcement technique. The high-level idea resembles that of Control-flow Locking (Bletsch et al., ACSAC '11): a sequence of basic blocks (function calls are allowed too) is wrapped with a "set" operation (in the beginning) and a "check" operation (at the end). The set operation basically sets a value into a register, while the check operation checks if the value of that particular register is the expected one. If the assertion fails, the whole enclave service is terminated.

The authors implemented Liveries by reserving a register, `%r15`, for the new API of their security architecture, while they also patched the SGX SDK so that `%r15` is not used in assembly code, replaced `libm` with `openlibm`, and compiled OpenSSL with `no-asm`, again to avoid assembly code that potentially uses `%r15`. In addition they wrapped all invocations of `EGETKEY` and `EREPORT` with sblocks, as well as the SM itself, and extended the `malloc` and `free` functions of `tlibc` so that the special areas (`MEASURE_AREA`,
`TMP_AREA`) can be handled accordingly. Interestingly, the authors also formally verified the sblock-wrapped code (TCB) using SMACK, proving absence of memory-safety errors and atomicity.

Lastly, in order to evaluate Liveries, the authors used nBench to assess the overhead of their design, achieving ~6% worst-case slowdown on nBench. Next, they ported KANN (a lightweight and standalone NN C library) in SGX, and used it to measure the overhead of Liveries in various NN tasks, but also compare Liveries with the naive approach of creating and destroying an enclave on a per-user "request/task". As expected, re: the latter, Liveries can be faster by a factor of hundreds of times, while as far as the impact of Liveries on real-world studies is concerned, the authors measured an average overhead of ~5% on various NN tasks (via KANN).

### Strengths

- [+] Interesting problem.
- [+] Promising design.
- [+] New security architecture.

### Weaknesses

- [-] Certain (claimed/assumed) security guarantees do not hold.

### Detailed comments for authors

Overall, the paper is well-written and presents an interesting SGX security architecture for enclaves that need to be shared by multiple, untrusted users.
The gist of Liveries is to effectively allow the _time-sharing_ of the enclave, but by avoiding the naive approach of creating and destroying an enclave for serving each user request separately.

Most of the important properties (P0, P1, partially P2, and P5) are enforced via ESC by configuring the enclave accordingly -- and various SGX1 features, such as the fact that mem. protection policy is part of the enclave measurement, `TCSNUM = 1`, `NSSA = 1`, _etc._, come in handy -- and so there's nothing novel about that part. However, the main issues of the paper are the
following:

1. sblocks: P3 and P2 (partially), as well as any other piece of code that needs to execute, uninterrupted, to completion, is protected via the sblocks mechanism. However, given that code-reuse attacks are within the scope of the threat model considered by the authors, it's unclear how this scheme guarantees the execution of a set of basic blocks from `entry` to `exit`. What prevents a code-reuse attack, which stems from the non-verified part(s) of the enclave code (more about this later; see pt. `2`), from loading the expected value in `%r15` and jumping in the middle on a piece of code that is protected from an sblock (bypassing a check in the beginning, skipping a critical operation, _etc._)? In Sec. 3.2, the authors mention the following: "To control those instructions, the ESC first finds them from all the code in the enclave (service, SM and SGX SDK), and then builds a protective sblock for each of them." and "We also remove their occurrences in the middle of instructions, through adding NOP and recompiling the code." (footnote 3). This is ok, for `ENCLU`, but what about all other gadgets re: `%r15`? Also, note that it's not enough to remove every occurrence of `%r15` from aligned instructions, as gadgets that operate on `%r15` (or any other register) can be part of overlapping gadgets.

2. Only the sblock-wrapped code is verified by SMACK, and so the rest of the enclave code can, of course, be vulnerable to mem. safety issues, atomicity violations, _etc._ -- and, in general, this (verification) is something that can be proven for a specific setting (i.e., the current one assumed by the authors), but what about every other potential use of this architecture? Is the bounded reachability approach guaranteed to prove the required properties for
*any* piece of enclave-application code?

Overall, Liveries presents an interesting design on how to put together a time-sharing enclave in a way that it's compatible with SGX (in terms of security guarantees). However, the sblock primitive is not enforcing a particular control flow in all cases, and so the authors need to address this
accordingly: by verifying the enclave-application code from being `%r15` gadget free, perhaps limiting certain program features a bit more (for instance, disallow indirect dispatch code), and so forth.

### Requested changes

(See pt. `1` and `2` in "_Detailed comments for authors_".)

### Questions for authors' response

(See pt. `1` and `2` in "_Detailed comments for authors_".)
