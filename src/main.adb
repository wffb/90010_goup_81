--Author: Lisong Xiao, Bo Huang, Hongjian Zhu



--  Task 1, Question 1:
--  The Spatial package defines Position and Velocity as separate Ada derived types
--  (both derived from Vector.Vector). This means Ada's strong type system treats them
--  as entirely distinct: a Position value cannot be passed where a Velocity is expected,
--  and vice versa, without an explicit conversion.
--
--  If everything were Vector.Vector, the following call would compile silently:
--
--    Univ.Add_Item (U,
--                   Univ.Get_Velocity (U, 1),   -- wrong: should be Position
--                   Univ.Get_Position (U, 1),   -- wrong: should be Velocity
--                   Initial_Radii (1));
--
--  With separate types, this mistake is caught at compile time because the argument
--  types do not match the parameter types of Add_Item (pos : Spatial.Position;
--  vel : Spatial.Velocity). Using Vector.Vector for both would allow this logical
--  error (treating a velocity as a position and vice versa) to go undetected.

--  Task 1, Question 2:
--  Each precondition in universe.ads guards against a specific runtime error:
--
--  * Get_Position, Get_Velocity, Get_Radius
--      Pre => Index >= 1 and then Index <= Item_Count (U)
--    Without this, accessing U.items(Index) when Index < 1 or Index > item_count
--    would violate the array index range and raise Constraint_Error at runtime.
--    Item_Count(U) may be less than Max_Items, so indices beyond it are uninitialised
--    slots that must not be read.
--
--  * Add_Item
--      Pre => Item_Count (U) < Max_Items
--    Without this, calling Add_Item when item_count is already Max_Items would
--    attempt to write to U.items(Max_Items + 1), which is beyond the array bounds,
--    raising Constraint_Error. It would also push item_count outside its declared
--    range 0 .. Max_Items, causing a range check failure.
--
--  * Reflect_Velocity_X, Reflect_Velocity_Y
--      Pre => Index >= 1 and then Index <= Item_Count (U)
--    Without this, modifying U.items(Index).vel when Index is out of the valid item
--    range would be an out-of-bounds array write, raising Constraint_Error. It would
--    also corrupt an uninitialised slot in the array.

--  Task 7 Reflection:
--  An early halt does not prove that the full wall-bouncing simulation would
--  definitely collide if it continued running -- a false halt is possible.
--
--  Task 6 establishes a one-way implication: if No_Future_Collision_Pair
--  holds, then the current frame is guaranteed to be collision-free. However,
--  the converse is not proved. When No_Future_Collision_Pair is false and the
--  simulation halts, this does not mean a collision would inevitably occur in
--  the full bouncing simulation.
--
--  The reason is that No_Future_Collision_Pair evaluates only the straight-line
--  trajectories under the velocities current since the last Reset_Universe. It
--  cannot anticipate future wall bounces. A bounce occurring before the
--  predicted collision time could redirect one or both objects, avoiding the
--  collision entirely.
--
--  This makes the halt condition conservative: the simulation guarantees
--  safety (no collision will occur during any executed frame) at the cost of
--  liveness (it may terminate early even when continuation would have been
--  safe).

--  Therefore, the answer to the question is: No. An early halt does
--  not guarantee that a collision would have occurred. The check is
--  sound but not complete.

--  Use of Generative AI: Claude and Codex were used to assist with drafting
--  the SPARK specifications, reflection, and ghost lemmas. The final code was
--  validated with alr build and gnatprove --level=2.

with Universe;
with Spatial;
with Vector; use Vector;
with Collision_Math;
with Display;
with Ada.Text_IO;
with Ada.Numerics.Big_Numbers.Big_Reals;
use Ada.Numerics.Big_Numbers.Big_Reals;

procedure Main with SPARK_Mode is
   use type Spatial.Velocity;
   use type Spatial.Position;
   package Univ is new Universe (10);

   package FC is new Float_Conversions (Float);
   package Disp is new Display (Univ, Max_Frames => 5500);

   U : Univ.Universe;

   Arena_X_Min : constant Big_Real := FC.To_Big_Real (-100.0);
   Arena_X_Max : constant Big_Real := FC.To_Big_Real (100.0);
   Arena_Y_Min : constant Big_Real := FC.To_Big_Real (-50.0);
   Arena_Y_Max : constant Big_Real := FC.To_Big_Real (50.0);

   Initial_Positions : array (1 .. 2) of Spatial.Position :=
     (Spatial.To_Position
        ((X => FC.To_Big_Real (0.0), Y => FC.To_Big_Real (5.0))),
      Spatial.To_Position
        ((X => FC.To_Big_Real (0.0), Y => FC.To_Big_Real (-5.0))));

   Initial_Velocities : array (1 .. 2) of Spatial.Velocity :=
     (Spatial.To_Velocity
        ((X => FC.To_Big_Real (0.4), Y => FC.To_Big_Real (0.3))),
      Spatial.To_Velocity
        ((X => FC.To_Big_Real (1.0), Y => FC.To_Big_Real (-0.7))));

   Initial_Radii : constant array (1 .. 2) of Big_Real :=
     (FC.To_Big_Real (2.0), FC.To_Big_Real (2.0));

   Tick_Count : Big_Real := To_Big_Real (0);

   function Position_Invariant (U : Univ.Universe) return Boolean is
     (Univ.Item_Count (U) = 2
      and then Tick_Count >= To_Big_Real (0)
      and then
        (for all I in 1 .. 2 =>
           Univ.Get_Position (U, I) =
             Spatial.To_Position
               (Vector.Add
                  (Spatial.To_Vector (Initial_Positions (I)),
                   Vector.Scale
                     (Spatial.Vel_To_Vector (Initial_Velocities (I)),
                      Tick_Count)))
           and then Univ.Get_Velocity (U, I) = Initial_Velocities (I)
           and then Univ.Get_Radius   (U, I) = Initial_Radii (I)));

   function Squared_Dist
     (U : Univ.Universe; I, J : Integer) return Big_Real is
       (Vector.Dot
          (Vector.Sub
             (Spatial.To_Vector (Univ.Get_Position (U, I)),
              Spatial.To_Vector (Univ.Get_Position (U, J))),
           Vector.Sub
             (Spatial.To_Vector (Univ.Get_Position (U, I)),
              Spatial.To_Vector (Univ.Get_Position (U, J))))) with
      Pre => I >= 1 and then I <= Univ.Item_Count (U)
             and then J >= 1 and then J <= Univ.Item_Count (U);

   function Pair_Sep2
     (I, J : Integer) return Big_Real is
       ((Initial_Radii (I) + Initial_Radii (J)) *
        (Initial_Radii (I) + Initial_Radii (J))) with
      Pre => I in 1 .. 2 and then J in 1 .. 2;

   function No_Future_Collision_Pair (I, J : Integer) return Boolean is
     (not Collision_Math.Will_Collide_Vec
        (Vector.Sub
           (Spatial.To_Vector (Initial_Positions (I)),
            Spatial.To_Vector (Initial_Positions (J))),
         Vector.Sub
           (Spatial.Vel_To_Vector (Initial_Velocities (I)),
            Spatial.Vel_To_Vector (Initial_Velocities (J))),
         Pair_Sep2 (I, J)))
   with Pre => I in 1 .. 2 and then J in 1 .. 2;

   procedure Lemma_No_Collision_Pair
     (U : Univ.Universe; I, J : Integer)
   with
     Ghost,
     Pre =>
       Position_Invariant (U)
       and then I in 1 .. 2
       and then J in 1 .. 2
       and then Tick_Count >= To_Big_Real (0)
       and then No_Future_Collision_Pair (I, J),
     Post => Squared_Dist (U, I, J) > Pair_Sep2 (I, J)
   is
      T      : constant Big_Real := Tick_Count;
      P_I    : constant Vector.Vector :=
        Spatial.To_Vector (Univ.Get_Position (U, I));
      P_J    : constant Vector.Vector :=
        Spatial.To_Vector (Univ.Get_Position (U, J));
      Init_I : constant Vector.Vector :=
        Spatial.To_Vector (Initial_Positions (I));
      Init_J : constant Vector.Vector :=
        Spatial.To_Vector (Initial_Positions (J));
      Vel_I  : constant Vector.Vector :=
        Spatial.Vel_To_Vector (Initial_Velocities (I));
      Vel_J  : constant Vector.Vector :=
        Spatial.Vel_To_Vector (Initial_Velocities (J));
      S      : constant Vector.Vector := Vector.Sub (Init_I, Init_J);
      V      : constant Vector.Vector := Vector.Sub (Vel_I, Vel_J);
      Eps2   : constant Big_Real := Pair_Sep2 (I, J);
   begin
      pragma Assert
        (Univ.Get_Position (U, I) =
           Spatial.To_Position
             (Vector.Add (Init_I, Vector.Scale (Vel_I, T))));
      pragma Assert
        (Univ.Get_Position (U, J) =
           Spatial.To_Position
             (Vector.Add (Init_J, Vector.Scale (Vel_J, T))));
      pragma Assert (P_I = Vector.Add (Init_I, Vector.Scale (Vel_I, T)));
      pragma Assert (P_J = Vector.Add (Init_J, Vector.Scale (Vel_J, T)));

      Collision_Math.Lemma_Sq_Dist_Bridge
        (P_I, P_J, Init_I, Init_J, Vel_I, Vel_J, T);

      pragma Assert
        (not Collision_Math.Will_Collide_Vec (S, V, Eps2));
      pragma Assert (Eps2 >= To_Big_Real (0));

      Collision_Math.Check_Implies_Safe_Vec (S, V, Eps2, T);

      pragma Assert
        (Vector.Dot (Vector.Sub (P_I, P_J), Vector.Sub (P_I, P_J)) =
           Collision_Math.Sq_Dist_At_Vec (S, V, T));
      pragma Assert
        (Squared_Dist (U, I, J) =
           Vector.Dot (Vector.Sub (P_I, P_J), Vector.Sub (P_I, P_J)));
      pragma Assert (Squared_Dist (U, I, J) > Eps2);
   end Lemma_No_Collision_Pair;

   type Bounce_Flags is record
      X : Boolean := False;
      Y : Boolean := False;
   end record;

   type Bounce_Array is array (1 .. 2) of Bounce_Flags;

   function Detect_Bounces
     (U : Univ.Universe) return Bounce_Array
     with Pre => Univ.Item_Count (U) = 2;

   function Detect_Bounces
     (U : Univ.Universe) return Bounce_Array
   is
      Result : Bounce_Array := (others => (X => False, Y => False));
   begin
      for Item in 1 .. 2 loop
         declare
            P : constant Spatial.Position :=
              Univ.Get_Position (U, Item);
            R : constant Big_Real := Univ.Get_Radius (U, Item);
         begin
            if Spatial.Pos_X (P) + R > Arena_X_Max
              or else Spatial.Pos_X (P) - R < Arena_X_Min
            then
               Result (Item).X := True;
            end if;
            if Spatial.Pos_Y (P) + R > Arena_Y_Max
              or else Spatial.Pos_Y (P) - R < Arena_Y_Min
            then
               Result (Item).Y := True;
            end if;
         end;
      end loop;
      return Result;
   end Detect_Bounces;

   procedure Print_Collision (Frame : Integer);

   procedure Print_Collision (Frame : Integer)
     with SPARK_Mode => Off
   is
   begin
      Ada.Text_IO.Put_Line
        ("Collision will occur after bounce at frame"
         & Integer'Image (Frame));
      for Item in 1 .. 2 loop
         declare
            V : constant Vector.Vector :=
              Spatial.Vel_To_Vector (Initial_Velocities (Item));
            P : constant Spatial.Position :=
              Initial_Positions (Item);
         begin
            Ada.Text_IO.Put_Line
              ("  Item" & Integer'Image (Item)
               & " pos=("
               & To_String (Spatial.Pos_X (P)) & ", "
               & To_String (Spatial.Pos_Y (P)) & ")"
               & " vel=("
               & To_String (V.X) & ", "
               & To_String (V.Y) & ")");
         end;
      end loop;
      Ada.Text_IO.Put_Line
        ("  Sep2=" & To_String (Pair_Sep2 (1, 2)));
   end Print_Collision;

   procedure Reset_Universe
     with Post => Position_Invariant (U)
   is
   begin
      Tick_Count := To_Big_Real (0);
      Univ.Init (U);
      Univ.Add_Item (U,
                     Initial_Positions (1),
                     Initial_Velocities (1),
                     Initial_Radii (1));
      Univ.Add_Item (U,
                     Initial_Positions (2),
                     Initial_Velocities (2),
                     Initial_Radii (2));
   end Reset_Universe;

begin
   Reset_Universe;

   if not No_Future_Collision_Pair (1, 2) then
      return;
   end if;

   for Frame in 1 .. 5000 loop
      pragma Loop_Invariant (Position_Invariant (U));
      pragma Loop_Invariant (Tick_Count >= To_Big_Real (0));
      pragma Loop_Invariant (No_Future_Collision_Pair (1, 2));

      Lemma_No_Collision_Pair (U, 1, 2);
      pragma Assert (Squared_Dist (U, 1, 2) > Pair_Sep2 (1, 2));

      Disp.Capture (U);
      Univ.Tick (U);
      Tick_Count := Tick_Count + To_Big_Real (1);

      declare
         Flags : constant Bounce_Array := Detect_Bounces (U);
      begin
         if Flags (1).X or else Flags (1).Y
           or else Flags (2).X or else Flags (2).Y
         then
            for Item in 1 .. 2 loop
               pragma Loop_Invariant (Univ.Item_Count (U) = 2);
               if Flags (Item).X then
                  Univ.Reflect_Velocity_X (U, Item);
               end if;
               if Flags (Item).Y then
                  Univ.Reflect_Velocity_Y (U, Item);
               end if;
            end loop;
            Initial_Positions :=
              (Univ.Get_Position (U, 1),
               Univ.Get_Position (U, 2));
            Initial_Velocities :=
              (Univ.Get_Velocity (U, 1),
               Univ.Get_Velocity (U, 2));

            Reset_Universe;

            if not No_Future_Collision_Pair (1, 2) then
               exit;
            end if;
         end if;
      end;
   end loop;

   Disp.Capture (U);
   Disp.Save ("simulation.html",
              Arena_X_Min, Arena_X_Max,
              Arena_Y_Min, Arena_Y_Max);
   Ada.Text_IO.Put_Line ("Wrote simulation.html");
end Main;
