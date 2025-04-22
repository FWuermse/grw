#import "@preview/diagraph:0.3.2": *

#let exgraph = (size) => raw-render(
```dot
digraph G {
    node [fontname = "Arial"];
    node [shape=plaintext];
    
    FinalS [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="110" HEIGHT="30">(p → q) ∧ (p → q)</TD>
                <TD WIDTH="300">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">←</TD></TR>
                        <TR><TD HEIGHT="15">s6 ≜ ?s6 ((p → q) ∧ (p → q)) ((q → q) ∧ (q → q)) s5</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="110">(q → q) ∧ (q → q)</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?s6, ?s5, ?r11 ,?s4,?r6, ?s2, ?r4, ?s1, ?r2, ?p1, ?r1, ?p2, ?r3, ?p3, ?r5, ?s5, ?r10, ?s3, ?r8, ?p4, ?r7, ?p5, ?r9}</TD>
            </TR>
        </TABLE>
    >];
    Final [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="110" HEIGHT="30">(p → q) ∧ (p → q)</TD>
                <TD WIDTH="300">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r11</TD></TR>
                        <TR><TD HEIGHT="15">s5 ≜ ?s5 ((p → q) ∧) ((q → q) ∧) s4 (p → q) (q → q) s3</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="110">(q → q) ∧ (q → q)</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?s5, ?r11 ,?s4,?r6, ?s2, ?r4, ?s1, ?r2, ?p1, ?r1, ?p2, ?r3, ?p3, ?r5, ?s5, ?r10, ?s3, ?r8, ?p4, ?r7, ?p5, ?r9}</TD>
            </TR>
        </TABLE>
    >];
    A [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="60" HEIGHT="30">(p → q) ∧</TD>
                <TD WIDTH="190">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r6</TD></TR>
                        <TR><TD HEIGHT="15">s4 ≜ ?s4 (∧) (∧) ?p3 (p → q) (q → q) s2</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="60">(q → q) ∧</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?s4,?r6, ?s2, ?r4, ?s1, ?r2, ?p1, ?r1, ?p2, ?r3, ?p3, ?r5}</TD>
            </TR>
        </TABLE>
    >];
    B [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p → q</TD>
                <TD WIDTH="180">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r10</TD></TR>
                        <TR><TD HEIGHT="15">s5 ≜ ?s5 (p →) (q →) s3 q q ?p5</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q → q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?s5, ?r10, ?s3, ?r8, ?p4, ?r7, ?p5, ?r9}</TD>
            </TR>
        </TABLE>
    >];
    C [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p → q</TD>
                <TD WIDTH="90">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r4</TD></TR>
                        <TR><TD HEIGHT="15">s2 ≜ ?s2 (p →) (q →) s1 q q ?p2 </TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q → q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?s2, ?r4, ?s1, ?r2, ?p1, ?r1, ?p2, ?r3}</TD>
            </TR>
        </TABLE>
    >];
    D [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">∧</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r5</TD></TR>
                        <TR><TD HEIGHT="15">?p3</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">∧</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p3, ?r5}</TD>
            </TR>
        </TABLE>
    >];
    F [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p →</TD>
                <TD WIDTH="110">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r2</TD></TR>
                        <TR><TD HEIGHT="15">s1 ≜ ?s1 (→) (→) ?p1 p q h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q →</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?s1, ?r2, ?p1, ?r1}</TD>
            </TR>
        </TABLE>
    >];
    E [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">q</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r3</TD></TR>
                        <TR><TD HEIGHT="15">?p2</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p2, ?r3}</TD>
            </TR>
        </TABLE>
    >];
    G [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">p</TD>
                <TD WIDTH="20">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">=</TD></TR>
                        <TR><TD HEIGHT="15">h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {}</TD>
            </TR>
        </TABLE>
    >];
    H [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">→</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r1</TD></TR>
                        <TR><TD HEIGHT="15">?p1</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">→</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p1, ?r1} </TD>
            </TR>
        </TABLE>
    >];
    J [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p →</TD>
                <TD WIDTH="110">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r8</TD></TR>
                        <TR><TD HEIGHT="15">s3 ≜ ?s3 (→) (→) ?p4 p q h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q →</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?s3, ?r8, ?p4, ?r7} </TD>
            </TR>
        </TABLE>
    >];
    I [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">q</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r9</TD></TR>
                        <TR><TD HEIGHT="15">?p5</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p5, ?r9}</TD>
            </TR>
        </TABLE>
    >];
    K [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">p</TD>
                <TD WIDTH="20">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">=</TD></TR>
                        <TR><TD HEIGHT="15">h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {}</TD>
            </TR>
        </TABLE>
    >];
    L [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">→</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r7</TD></TR>
                        <TR><TD HEIGHT="15">?p4</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">→</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p4, ?r7}</TD>
            </TR>
        </TABLE>
    >];
    I -> B
    J -> B
    K -> J
    L -> J
    G -> F
    H -> F
    F -> C
    E -> C
    D -> A
    C -> A
    A -> Final
    B -> Final
    Final -> FinalS
}
```, width: size, engine: "dot"
)

#let updatedgraph = (size) => raw-render(
```dot
digraph G {
    node [fontname = "Arial"];
    node [shape=plaintext];
    
    Final [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="110" HEIGHT="30">(p → q) ∧ (p → q)</TD>
                <TD WIDTH="300">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">←</TD></TR>
                        <TR><TD HEIGHT="15">p3 ≜ ?p3 (q → p) (q → q) p1 (q → p) (q → q) p2</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="110">(q → q) ∧ (q → q)</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p3, ?p1, ?r1, ?p2, ?r2}</TD>
            </TR>
        </TABLE>
    >];
    A [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="60" HEIGHT="30">q → p</TD>
                <TD WIDTH="190">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r1</TD></TR>
                        <TR><TD HEIGHT="15">p1 ≜ ?p1 p q h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="60">q → q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p1, ?r1}</TD>
            </TR>
        </TABLE>
    >];
    B [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">q → p</TD>
                <TD WIDTH="180">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?r2</TD></TR>
                        <TR><TD HEIGHT="15">p2 ≜ ?p2 p q h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q → q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {?p2, ?r2}</TD>
            </TR>
        </TABLE>
    >];
    E [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="10" HEIGHT="5">q</TD>
                <TD WIDTH="10">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">id</TD></TR>
                    </TABLE>
                </TD>
            </TR>
        </TABLE>
    >];
    H [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="5">→</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">id</TD></TR>
                    </TABLE>
                </TD>
            </TR>
        </TABLE>
    >];
    G [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">p</TD>
                <TD WIDTH="20">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">=</TD></TR>
                        <TR><TD HEIGHT="15">h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; := {}</TD>
            </TR>
        </TABLE>
    >];
    I [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="10" HEIGHT="5">q</TD>
                <TD WIDTH="10">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">id</TD></TR>
                    </TABLE>
                </TD>
            </TR>

        </TABLE>
    >];
    L [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="5">→</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="5">id</TD></TR>
                    </TABLE>
                </TD>
            </TR>
        </TABLE>
    >];
    K [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">p</TD>
                <TD WIDTH="20">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">=</TD></TR>
                        <TR><TD HEIGHT="15">h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="5">&#936; := {}</TD>
            </TR>
        </TABLE>
    >];
    I -> B
    K -> B
    L -> B
    G -> A
    H -> A
    E -> A
    A -> Final
    B -> Final
}
```, width: size, engine: "dot"
)