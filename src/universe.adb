--Author: Lisong Xiao, Bo Huang, Hongjian Zhu

with Ada.Text_IO; with Ada.Integer_Text_IO;

package body Universe with SPARK_Mode is

   Zero_Vec  : constant Vector.Vector :=
     (X => To_Big_Real (0), Y => To_Big_Real (0));
   Zero_Pos  : constant Spatial.Position := Spatial.To_Position (Zero_Vec);
   Zero_Vel  : constant Spatial.Velocity := Spatial.To_Velocity (Zero_Vec);
   Zero_Item : constant Universe_Item :=
     (pos => Zero_Pos, vel => Zero_Vel, rad => To_Big_Real (0));

   procedure Init (U : out Universe) is
   begin
      U := (item_count => 0, items => (others => Zero_Item));
   end Init;

   procedure Add_Item
     (U   : in out Universe;
      pos : Spatial.Position;
      vel : Spatial.Velocity;
      rad : Big_Real)
   is
   begin
      U.item_count := U.item_count + 1;
      U.items (U.item_count) := (pos => pos, vel => vel, rad => rad);
   end Add_Item;

   procedure Reflect_Velocity_X
     (U : in out Universe; Index : Integer) is
   begin
      U.items (Index).vel := Spatial.Negate_Vel_X (U.items (Index).vel);
   end Reflect_Velocity_X;

   procedure Reflect_Velocity_Y
     (U : in out Universe; Index : Integer) is
   begin
      U.items (Index).vel := Spatial.Negate_Vel_Y (U.items (Index).vel);
   end Reflect_Velocity_Y;

   procedure Print (U : Universe)
     with SPARK_Mode => Off
   is
   begin
      for I in U.items'First .. U.item_count loop
         Ada.Text_IO.Put ("Item: ");
         Ada.Integer_Text_IO.Put (I);
         Ada.Text_IO.Put (": pos: (");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_X (U.items (I).pos)));
         Ada.Text_IO.Put (",");
         Ada.Text_IO.Put
           (To_String (Spatial.Pos_Y (U.items (I).pos)));
         Ada.Text_IO.Put (")");
         Ada.Text_IO.New_Line;
      end loop;
   end Print;

   procedure Tick (U : in out Universe) is
   begin
      for I in 1 .. U.item_count loop
         U.items (I).pos := Spatial.Move (U.items (I).pos, U.items (I).vel);
         pragma Loop_Invariant
           (U.item_count = U'Loop_Entry.item_count
            and then
              (for all J in 1 .. I =>
                 U.items (J).pos =
                   Spatial.Move (U'Loop_Entry.items (J).pos,
                                 U'Loop_Entry.items (J).vel)
                 and then U.items (J).vel = U'Loop_Entry.items (J).vel
                 and then U.items (J).rad = U'Loop_Entry.items (J).rad)
            and then
              (for all J in I + 1 .. U.item_count =>
                 U.items (J).pos = U'Loop_Entry.items (J).pos
                 and then U.items (J).vel = U'Loop_Entry.items (J).vel
                 and then U.items (J).rad = U'Loop_Entry.items (J).rad));
      end loop;
   end Tick;

end Universe;
