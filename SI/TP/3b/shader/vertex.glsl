// Version d'OpenGL
#version 330

// Donnees d'entree
//layout(location=0) in vec3 in_position;
in vec3 in_position;
in vec3 in_color;
in vec3 in_normal;

uniform int cur_time;

// Donnees de sortie
out vec4 my_color;
out vec4 my_position;
out vec4 my_normals;

// Parametres
uniform mat4 ModelMatrix;
uniform mat4 ViewMatrix;
uniform mat4 ProjectionMatrix;

// Fonction appellee pour chaque sommet
void main()
{
  // Affectation de la position du sommet
  // gl_Position est defini par défaut dans GLSL
  //gl_Position = ProjectionMatrix * ViewMatrix * ModelMatrix * vec4(in_position, 1.0);;
  gl_Position = ProjectionMatrix * ViewMatrix * ModelMatrix * vec4((in_position + vec3(sin(cur_time + 1), sin(cur_time), sin(cur_time + 2))), 1.0);
  my_position = ProjectionMatrix * ViewMatrix * ModelMatrix * vec4(in_position, 1.0);

  //my_color = vec4((in_position + vec3(1,1,1))*0.5, 1.0);
  my_color = vec4(in_color, 1.0);

  my_normals = vec4(in_normal, 1.0);
}
