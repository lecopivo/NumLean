namespace NumLean

class HasDeviceType (device : Name) (hostType : Type) (deviceType : outParam Type) where
  toDevice : hostType → deviceType
  toHost : deviceType → hostType

export HasDeviceType (toDevice toHost)

def Device (device : Name) (hostType : Type)
    {deviceType} [HasDeviceType device hostType deviceType] := deviceType

class DeviceMonad (device : Name) (m : outParam (Type → Type)) where
  bind {A B : Type} {A' B'} [HasDeviceType device A A'] [HasDeviceType device B B']
    (x : m A') (f : A' → m B') : m B'
  pure {A : Type} [HasDeviceType device A A']
    (x : A') : m A'

def DeviceM (device : Name) {m : Type → Type} [DeviceMonad device m]
  (A : Type) {A'} [HasDeviceType device A A'] :=
  m A'

variable {d : Name}
  {A A'} [HasDeviceType d A A']
  {B B'} [HasDeviceType d B B']
  {m} [DeviceMonad d m]

namespace Device

def pure (x : Device d A) : DeviceM d A := DeviceMonad.pure d (A:=A) x

def bind (x : DeviceM d A) (f : Device d A → DeviceM d B) : DeviceM d B :=
  DeviceMonad.bind (A:=A) (B:=B) d x f

end Device

def HasDeviceImpl (f : A → B) (g : Device d A → Device d B) : Prop :=
  ∀ x, f x = toHost d (g (toDevice d x))

def HasDeviceImplM (f : A → B) (g : Device d A → DeviceM d B) : Prop :=
  ∀ x, Device.pure (toDevice d (f x)) = (g (toDevice d x))

def HasDeviceVal (a : A) (a' : Device d A) : Prop :=
  toHost d a' = a

namespace HasDeviceVal

-- @[device_compile]
theorem toHost_hadDeviceVal (a' : Device d A) : HasDeviceVal (toHost d a') a' := rfl

end HasDeviceVal
