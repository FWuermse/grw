#import "@preview/diagraph:0.3.2": *
#raw-render(
  ```dot
digraph G {
    size="100,100!"
    node [shape=plaintext];
    
    Final [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="100" HEIGHT="30">(p → q) ∧ (p → q)</TD>
                <TD WIDTH="260">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77814</TD></TR>
                        <TR><TD HEIGHT="15">?s5 ((p → q) ∧) ((q → q) ∧) ?s4 (p → q) (q → q) ?s3</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="100">(q → q) ∧ (q → q)</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : ?s5, ?m.77814 ,?s4,?m.77695, ?s2, ?m.77667, ?s1, ?m.77622, ?p1, ?m.77604, ?p2, ?m.77650, p3, ?m.77585, ?s5, ?m.77787, ?s3, ?m.77742, ?p4, ?m.77725, ?p5, ?m.77770}</TD>
            </TR>
        </TABLE>
    >];
    A [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="60" HEIGHT="30">(p → q) ∧</TD>
                <TD WIDTH="190">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77695</TD></TR>
                        <TR><TD HEIGHT="15">?s4 (∧) (∧) ?s2 (p → q) (q → q) ?s3.2</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="60">(q → q) ∧</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {?s4,?m.77695, ?s2, ?m.77667, ?s1, ?m.77622, ?p1, ?m.77604, ?p2, ?m.77650, p3, ?m.77585}</TD>
            </TR>
        </TABLE>
    >];
    B [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p → q</TD>
                <TD WIDTH="90">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77787</TD></TR>
                        <TR><TD HEIGHT="15">?s5 (p →) (q →) ?s3 q q ?p5</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q → q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {?s5, ?m.77787, ?s3, ?m.77742, ?p4, ?m.77725, ?p5, ?m.77770}</TD>
            </TR>
        </TABLE>
    >];
    C [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p → q</TD>
                <TD WIDTH="90">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77667</TD></TR>
                        <TR><TD HEIGHT="15">?s2 (p →) (q →) ?s1 </TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q → q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {?s2, ?m.77667, ?s1, ?m.77622, ?p1, ?m.77604, ?p2, ?m.77650}</TD>
            </TR>
        </TABLE>
    >];
    D [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="10" HEIGHT="30">∧</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77585</TD></TR>
                        <TR><TD HEIGHT="15">?p3 (∧)</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="10">∧</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {p3, ?m.77585}</TD>
            </TR>
        </TABLE>
    >];
    F [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p →</TD>
                <TD WIDTH="110">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77622</TD></TR>
                        <TR><TD HEIGHT="15">?s1 (→) (→) ?p1 p q h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q →</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {?s1, ?m.77622, ?p1, ?m.77604}</TD>
            </TR>
        </TABLE>
    >];
    E [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="10" HEIGHT="30">q</TD>
                <TD WIDTH="10">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77650</TD></TR>
                        <TR><TD HEIGHT="15">?p2</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="10">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {?p2, ?m.77650}</TD>
            </TR>
        </TABLE>
    >];
    G [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="10" HEIGHT="30">p</TD>
                <TD WIDTH="10">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">=</TD></TR>
                        <TR><TD HEIGHT="15">h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="10">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {}</TD>
            </TR>
        </TABLE>
    >];
    H [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">→</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77604</TD></TR>
                        <TR><TD HEIGHT="15">?p1 (→)</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">→</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {p1, ?m.77604} </TD>
            </TR>
        </TABLE>
    >];
    J [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="40" HEIGHT="30">p →</TD>
                <TD WIDTH="110">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77742</TD></TR>
                        <TR><TD HEIGHT="15">?s3 (→) (→) ?p4 p q h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="40">q →</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; :{?s3, ?m.77742, ?p4, ?m.77725} </TD>
            </TR>
        </TABLE>
    >];
    I [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="10" HEIGHT="30">q</TD>
                <TD WIDTH="10">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77770</TD></TR>
                        <TR><TD HEIGHT="15">?p5</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="10">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {?p5, ?m.77770}</TD>
            </TR>
        </TABLE>
    >];
    K [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="10" HEIGHT="30">p</TD>
                <TD WIDTH="10">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">=</TD></TR>
                        <TR><TD HEIGHT="15">h</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="10">q</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {}</TD>
            </TR>
        </TABLE>
    >];
    L [label=<
        <TABLE BORDER="0" CELLBORDER="1" CELLSPACING="0">
            <TR>
                <TD WIDTH="20" HEIGHT="30">→</TD>
                <TD WIDTH="40">
                    <TABLE BORDER="0" CELLBORDER="0" CELLSPACING="0">
                        <TR><TD HEIGHT="15">?m.77725</TD></TR>
                        <TR><TD HEIGHT="15">p4 ≜ ?p4 (→)</TD></TR>
                    </TABLE>
                </TD>
                <TD WIDTH="20">→</TD>
            </TR>
            <TR>
                <TD COLSPAN="3" HEIGHT="10">&#936; : {?p4, ?m.77725}</TD>
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
}
```, width: 40em
)